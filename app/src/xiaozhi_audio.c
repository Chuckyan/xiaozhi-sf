/*
 * SPDX-FileCopyrightText: 2024-2025 SiFli Technologies(Nanjing) Co., Ltd
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include <rtthread.h>
#include "lwip/api.h"
#include "lwip/dns.h"
#include "lwip/apps/mqtt_priv.h"
#include "lwip/apps/mqtt.h"
#include "lwip/udp.h"
#include "lwip/tcpip.h"
#include "xiaozhi_mqtt.h"
#include "bf0_hal.h"
#include "button.h"
#include "os_adaptor.h"
#include "opus_types.h"
#include "opus_multistream.h"
#include "os_support.h"
#include "audio_server.h"
#include "drv_audprc.h"
#include "mem_section.h"
#ifdef PKG_XIAOZHI_USING_AEC
    #include "webrtc/common_audio/vad/include/webrtc_vad.h"
    #include "sifli_resample.h"
#endif
#include "bts2_app_inc.h"
#include "ble_connection_manager.h"
#include "bt_connection_manager.h"
#include "bt_env.h"
#include "xiaozhi_client_public.h"
#include "opus.h"
#include "debug.h"
#include "opus_private.h"
#include "../weather/weather.h"
#include "gui_app_pm.h"
#include "lv_display.h"
#include "xiaozhi_ui.h"
#include "xiaozhi_websocket.h"
#include "xiaozhi_audio.h"
#include "log.h"

#undef LOG_TAG
#define LOG_TAG "xz"
#define DBG_TAG "xz"
#define DBG_LVL LOG_LVL_INFO
#define XZ_THREAD_NAME "xiaozhi"
#define XZ_OPUS_STACK_SIZE (32 * 1024)
#define XZ_EVENT_MIC_RX (1 << 0)
#define XZ_EVENT_SPK_TX (1 << 1)
#define XZ_EVENT_DOWNLINK (1 << 2)
#define XZ_EVENT_EXIT (1 << 3)
#define MQTT_RECONNECT 12

#define XZ_EVENT_ALL                                                           \
    (XZ_EVENT_MIC_RX | XZ_EVENT_SPK_TX | XZ_EVENT_DOWNLINK | XZ_EVENT_EXIT)

#define VOICE_STATE_IDLE 0
#define VOICE_STATE_WAIT_SPEAKING 1
#define VOICE_STATE_SPEAKING 2

#define VOICE_START_TIMES (XZ_MIC_FRAME_LEN / 320 * 2) /* 1 mic frames */
#define VOICE_STOP_TIMES 30

#define XZ_AUDIO_VERSION "xz_audio_verson: 1.0"

#ifdef XIAOZHI_USING_MQTT
    #define XZ_DEVICE_STATE mqtt_g_state
#else
    #define XZ_DEVICE_STATE web_g_state
#endif
extern rt_mailbox_t g_bt_app_mb;
extern uint8_t vad_enable;
extern uint8_t Initiate_disconnection_flag;
extern lv_obj_t *main_container;
extern lv_obj_t *standby_screen;

struct udp_pcb *udp_pcb;
xz_audio_t xz_audio;
bool g_ota_verified = true;

#if defined(__CC_ARM) || defined(__CLANG_ARM)
L2_RET_BSS_SECT_BEGIN(g_xz_opus_stack) // 6000地址
static uint32_t g_xz_opus_stack[XZ_OPUS_STACK_SIZE / sizeof(uint32_t)];
L2_RET_BSS_SECT_END
#else
static uint32_t
    g_xz_opus_stack[XZ_OPUS_STACK_SIZE / sizeof(uint32_t)] L2_RET_BSS_SECT(
        g_xz_opus_stack);
#endif

static void xz_opus_thread_entry(void *p);
static void audio_write_and_wait(xz_audio_t *thiz, uint8_t *data,
                                 uint32_t data_len);
static void xz_button_event_handler(int32_t pin, button_action_t action);
void xz_mic_open(xz_audio_t *thiz);
void xz_mic_close(xz_audio_t *thiz);
void xz_speaker_close(xz_audio_t *thiz);
void xz_speaker_open(xz_audio_t *thiz);

void xz_audio_send(uint8_t *data, int len)
{
    uint32_t nonce[4];
    uint8_t *p_nonce = (uint8_t *)&(nonce[0]);

    memcpy(p_nonce, &(g_xz_context.nonce[0]), sizeof(nonce));
    *(uint16_t *)(p_nonce + 2) = htons(len);
    *(uint32_t *)(p_nonce + 12) = htonl(++g_xz_context.local_sequence);
    // Encrypt data
    HAL_AES_init((uint32_t *)&(g_xz_context.key[0]), 16,
                 (uint32_t *)&(nonce[0]), AES_MODE_CTR);
    struct pbuf *pbuf =
        pbuf_alloc(PBUF_TRANSPORT, len + sizeof(nonce) + 32, PBUF_RAM);
    if (pbuf && g_xz_context.port)
    {
        uint8_t *payload = (uint8_t *)pbuf->payload;
        memcpy(payload, nonce, sizeof(nonce));
        payload += sizeof(nonce);
        HAL_AES_run(AES_ENC, data, payload, len);
        LOCK_TCPIP_CORE();
        udp_sendto(udp_pcb, pbuf, &(g_xz_context.udp_addr), g_xz_context.port);
        UNLOCK_TCPIP_CORE();
        pbuf_free(pbuf);
    }
}

void xz_udp_recv(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                 const ip_addr_t *addr, u16_t port)
{
    if (memcmp(addr, &(g_xz_context.udp_addr), sizeof(ip_addr_t)) == 0 &&
        port == g_xz_context.port)
    {
        uint8_t *data = (uint8_t *)p->payload;
        uint32_t nonce[4];
        uint32_t size = 0;
        uint32_t sequence = ntohl(*(uint32_t *)&data[12]);

        if (p->len < sizeof(nonce))
        {
            rt_kprintf("Invalid audio packet size: %u\n", p->len);
            goto end;
        }
        if (data[0] != 0x01)
        {
            rt_kprintf("Invalid audio packet type: %x", data[0]);
            goto end;
        }
        if (sequence < g_xz_context.remote_sequence)
        {
            // 当新对话流开始（序列号重置为1）或序列号跳变时，自动重置同步序列号
            if (sequence <= 10 || (g_xz_context.remote_sequence - sequence > 100))
            {
                g_xz_context.remote_sequence = sequence;
            }
            else
            {
                rt_kprintf(
                    "Received audio packet with old sequence: %lu, expected: %lu\n",
                    sequence, g_xz_context.remote_sequence);
                goto end;
            }
        }
        if (sequence != g_xz_context.remote_sequence + 1)
        {
            rt_kprintf("Received audio packet with wrong sequence: %lu, "
                       "expected: %lu\n",
                       sequence, g_xz_context.remote_sequence + 1);
            g_xz_context.remote_sequence = sequence;
        }
        else
        {
            g_xz_context.remote_sequence = sequence;
        }
        memcpy(&(nonce[0]), data, sizeof(nonce));
        data += sizeof(nonce);
        size = p->len - sizeof(nonce);
        xz_audio_downlink(data, size, &nonce[0], 1);
    end:
        pbuf_free(p);
    }
    else
    {
        rt_kprintf("invalid udp\n");
    }
}
#ifdef XIAOZHI_USING_MQT
void simulate_button_pressed()
{
    rt_kprintf("mqtt simulate_button_pressed pressed\r\n");
    if (Initiate_disconnection_flag) // 蓝牙主动断开不允许mic触发
    {
        rt_kprintf("Initiate_disconnection_flag\r\n");
        return;
    }
    xz_button_event_handler(BSP_KEY1_PIN, BUTTON_PRESSED);
}
void simulate_button_released()
{
    rt_kprintf("mqtt simulate_button_released released\r\n");
    if (Initiate_disconnection_flag)
    {
        return;
    }
    xz_button_event_handler(BSP_KEY1_PIN, BUTTON_RELEASED);
}
#else
RT_WEAK void simulate_button_pressed()
{
}
RT_WEAK void simulate_button_released()
{
}
#endif

static float g_mic_hpf_x = 0.0f;
static float g_mic_hpf_y = 0.0f;

static inline int16_t xz_mic_soft_clip(float in)
{
    if (in > 26000.0f)
    {
        float diff = in - 26000.0f;
        in = 26000.0f + diff / (1.0f + diff / 5000.0f);
    }
    else if (in < -26000.0f)
    {
        float diff = -in - 26000.0f;
        in = -26000.0f - diff / (1.0f + diff / 5000.0f);
    }
    if (in > 32767.0f) return 32767;
    if (in < -32768.0f) return -32768;
    return (int16_t)in;
}

static void xz_mic_dsp_process(int16_t *pcm, uint32_t samples, int is_speech)
{
    for (uint32_t i = 0; i < samples; i++)
    {
        float x = (float)pcm[i];
        // 1. 80Hz HPF (切除DC偏置与<80Hz低频风噪/震动噪)
        float y = 0.9695f * (g_mic_hpf_y + x - g_mic_hpf_x);
        g_mic_hpf_x = x;
        g_mic_hpf_y = y;

        // 2. 智能动态噪声门限 (非说话静音期衰减电路与环境底噪)
        if (!is_speech)
        {
            y *= 0.25f; // -12dB 抑噪
        }

        // 3. 麦克风输入软限幅防爆音
        pcm[i] = xz_mic_soft_clip(y);
    }
}

static int mic_callback(audio_server_callback_cmt_t cmd,
                        void *callback_userdata, uint32_t reserved)
{
    // this was called every 10ms
    xz_audio_t *thiz = &xz_audio;
    if (thiz->is_rx_enable && cmd == as_callback_cmd_data_coming)
    {
        // data lengh is 320 bytes, which is 10ms for 16k samplerate
        audio_server_coming_data_t *p = (audio_server_coming_data_t *)reserved;
#ifdef PKG_XIAOZHI_USING_AEC
        if (thiz->vad_enabled)
        {
            int ret = WebRtcVad_Process(thiz->handle, 16000, (int16_t *)p->data,
                                        p->data_len /
                                            2); // 检测是否是人声 返回1是人声
            // 运行麦克风预处理降噪算法（80Hz高通+静音期底噪门限+防爆音限幅）
            xz_mic_dsp_process((int16_t *)p->data, p->data_len / 2, ret);
            if (vad_enable) // 如果开起了不打断功能 1是不打断
            {
                if (XZ_DEVICE_STATE != kDeviceStateIdle)
                {
                    return 0; // 非待命状态不处理VAD
                }
            }
            if (VOICE_STATE_IDLE == thiz->voice_state)
            {
    #if !ALLOW_VAD_WHEN_SPEAKING
                if ((ret == 1))
    #else
                if ((ret == 1) && (XZ_DEVICE_STATE != kDeviceStateSpeaking))
    #endif
                {
                    LOG_I("idle --> wait speaking");
                    thiz->voice_stop_times = 0;
                    thiz->voice_state = VOICE_STATE_WAIT_SPEAKING;
                    thiz->voice_start_times = 0;
                }
                // return 0;
            }
            else if (VOICE_STATE_WAIT_SPEAKING == thiz->voice_state)
            {
                if (vad_enable) // 如果开起了不打断功能 1是不打断
                {
                    if (XZ_DEVICE_STATE == kDeviceStateSpeaking)
                    {
                        // xiaozhi is speaking, do not respond to mic input
                        LOG_I("speaking --> idle");
                        thiz->voice_start_times = 0;
                        thiz->voice_stop_times = 0;
                        thiz->voice_state = VOICE_STATE_IDLE;
                    }
                }
                if (ret)
                {
                    // voice
                    thiz->voice_stop_times = 0;
                    if (thiz->voice_start_times < VOICE_START_TIMES)
                    {
                        thiz->voice_start_times++;
                        // LOG_I("wait enough voice
                        // times=%d",thiz->voice_start_times);
                        rt_ringbuffer_put(thiz->rb_vad_cache, p->data,
                                          p->data_len);
                    }
                    else if (thiz->voice_start_times == VOICE_START_TIMES)
                    {
                        thiz->voice_start_times = 0;
                        thiz->voice_state = VOICE_STATE_SPEAKING;
                        LOG_I("call button pressed");
                        simulate_button_pressed();
                        uint8_t buf[320];
                        while (rt_ringbuffer_data_len(thiz->rb_vad_cache) >=
                               320)
                        {
                            rt_ringbuffer_get(thiz->rb_vad_cache, buf, 320);
                            rt_ringbuffer_put(thiz->rb_opus_encode_input, buf,
                                              320);
                        }
                        rt_ringbuffer_put(thiz->rb_opus_encode_input, p->data,
                                          p->data_len);
                        rt_ringbuffer_reset(thiz->rb_vad_cache);
                    }
                }
                else
                { // not voice
                    LOG_I("wait speaking --> idle");
                    thiz->voice_start_times = 0;
                    thiz->voice_stop_times = 0;
                    thiz->voice_state = VOICE_STATE_IDLE;
                    rt_ringbuffer_reset(thiz->rb_vad_cache);
                }
                return 0;
            }
            else if (VOICE_STATE_SPEAKING == thiz->voice_state)
            {
                if (ret == 1)
                {
                    LOG_I("speaking");
                    thiz->voice_stop_times = 0;
                }
                else
                {
                    LOG_I("not voice");
                    if (thiz->voice_stop_times < VOICE_STOP_TIMES)
                    {
                        thiz->voice_stop_times++;
                        LOG_I("wait no voice times=%d", thiz->voice_stop_times);
                    }
                    if (thiz->voice_stop_times == VOICE_STOP_TIMES)
                    {
                        LOG_I("speaking --> idle");
                        thiz->voice_stop_times = 0;
                        thiz->voice_start_times = 0;
                        thiz->voice_state = VOICE_STATE_IDLE;
                        LOG_I("call button released");
                        simulate_button_released();
                        return 0;
                    }
                }
            }
            else
            {
                RT_ASSERT(0);
            }
        }
#endif
        rt_ringbuffer_put(thiz->rb_opus_encode_input, p->data, p->data_len);
        thiz->mic_rx_count += 320;

        if (thiz->mic_rx_count >= XZ_MIC_FRAME_LEN)
        {
            thiz->mic_rx_count = 0;
            rt_event_send(thiz->event, XZ_EVENT_MIC_RX);
        }
    }
    return 0;
}

void xz_mic(int on)
{
    // Sample rate is 16K, each packet should be 60ms
    xz_audio_t *thiz = &xz_audio;
    if (on)
    {
        xz_mic_open(thiz);
    }
    else
    {
        xz_mic_close(thiz);
    }
}

void xz_speaker(int on)
{
    // Sample rate is g_xz_context.sample_rate(typical 24K),
    // each packet should be g_xz_context.frame_duration(typical 60ms)
    xz_audio_t *thiz = &xz_audio;
    if (on)
    {
        xz_speaker_open(thiz);
    }
    else
    {
        xz_speaker_close(thiz);
    }
}

#ifdef XIAOZHI_USING_MQTT
static void xz_button_event_handler(int32_t pin, button_action_t action)
{
    lv_display_trigger_activity(NULL);
    gui_pm_fsm(GUI_PM_ACTION_WAKEUP); // 唤醒设备
    rt_kprintf("in mqtt button handle2\n");
    // 如果当前处于KWS模式，则退出KWS模式
    if (g_kws_running)
    {
        rt_kprintf("KWS exit\n");
        g_kws_force_exit = 1;
    }
    static button_action_t last_action = BUTTON_RELEASED;
    rt_kprintf("button(%d) %d:", pin, action);
    if (last_action == action)
    {
        return;
    }
    last_action = action;

    if (action == BUTTON_PRESSED)
    {

        lv_obj_t *now_screen = lv_screen_active();
        rt_kprintf("pressed\r\n");
        rt_kprintf("mqtt按键->对话\n");
        if (now_screen == standby_screen)
        {
            ui_switch_to_xiaozhi_screen();
        }
        if (mqtt_g_state == kDeviceStateUnknown) // goodby唤醒
        {
            mqtt_hello(&g_xz_context);
        }
        if (mqtt_g_state == kDeviceStateSpeaking)
        {
            mqtt_g_state = kDeviceStateListening;
        }

        xiaozhi_ui_chat_status("聆听中...");
    }
    else if (action == BUTTON_RELEASED)
    {
        rt_kprintf("released\r\n");
        xiaozhi_ui_chat_status("待命中...");
    }
}

void xz_mqtt_button_init(void)
{
    static int initialized = 0;

    if (initialized == 0)
    {
        button_cfg_t cfg;
        cfg.pin = BSP_KEY1_PIN;

        cfg.active_state = BSP_KEY1_ACTIVE_HIGH;
        cfg.mode = PIN_MODE_INPUT;
        cfg.button_handler = xz_button_event_handler;
        int32_t id = button_init(&cfg);
        RT_ASSERT(id >= 0);
        RT_ASSERT(SF_EOK == button_enable(id));
        initialized = 1;
    }
}

void xz_audio_init()
{
    rt_kprintf("xz_audio_init\n");
    rt_kprintf("exit sniff mode\n");
    // bt_interface_exit_sniff_mode(
    //     (unsigned char *)&g_bt_app_env.bd_addr); // exit sniff mode
    // bt_interface_wr_link_policy_setting(
    //     (unsigned char *)&g_bt_app_env.bd_addr,
    //     BT_NOTIFY_LINK_POLICY_ROLE_SWITCH); // close role switch
    if (udp_pcb)
    {
        udp_remove(udp_pcb);
        udp_pcb = NULL;
    }
    audio_server_set_private_volume(AUDIO_TYPE_LOCAL_MUSIC, 6);
    xz_audio_decoder_encoder_open(0);

    xz_mqtt_button_init();
    udp_pcb = udp_new();
    g_xz_context.local_sequence = 0;
    g_xz_context.remote_sequence = 0;
    udp_recv(udp_pcb, xz_udp_recv, NULL);
}
#endif
typedef struct
{
    float b0, b1, b2;
    float a1, a2;
    float x1, x2;
    float y1, y2;
} xz_biquad_t;

// 4-band cascaded Biquad EQ tuned for LM4871M/TR amplifier + micro-speaker @ 24kHz
// Stage 0: HPF 120Hz (cut sub-bass, prevent LM4871 overload & cone rattle)
// Stage 1: Peaking 400Hz -2.5dB (cut boxy resonance)
// Stage 2: Peaking 3.5kHz +4.0dB (boost speech presence & consonant clarity/resolution)
// Stage 3: High Shelf 7.5kHz +3.0dB (boost 24kHz high frequency sparkle)
static xz_biquad_t g_xz_eq[4] = {
    {0.978030f, -1.956060f, 0.978030f, -1.955577f, 0.956541f, 0, 0, 0, 0},
    {0.985764f, -1.875830f, 0.900400f, -1.875830f, 0.886163f, 0, 0, 0, 0},
    {1.121630f, -0.964314f, 0.462428f, -0.964314f, 0.584058f, 0, 0, 0, 0},
    {1.141940f,  0.418640f, 0.223170f,  0.556850f, 0.226920f, 0, 0, 0, 0}
};

static inline int16_t xz_soft_clip(float in)
{
    if (in > 28000.0f)
    {
        float diff = in - 28000.0f;
        in = 28000.0f + diff / (1.0f + diff / 4767.0f);
    }
    else if (in < -28000.0f)
    {
        float diff = -in - 28000.0f;
        in = -28000.0f - diff / (1.0f + diff / 4767.0f);
    }
    if (in > 32767.0f) return 32767;
    if (in < -32768.0f) return -32768;
    return (int16_t)in;
}

static void xz_audio_dsp_process(int16_t *pcm, uint32_t samples)
{
    for (uint32_t i = 0; i < samples; i++)
    {
        float x = (float)pcm[i];
        for (int stage = 0; stage < 4; stage++)
        {
            xz_biquad_t *bq = &g_xz_eq[stage];
            float y = bq->b0 * x + bq->b1 * bq->x1 + bq->b2 * bq->x2 - bq->a1 * bq->y1 - bq->a2 * bq->y2;
            bq->x2 = bq->x1;
            bq->x1 = x;
            bq->y2 = bq->y1;
            bq->y1 = y;
            x = y;
        }
        pcm[i] = xz_soft_clip(x);
    }
}

static void audio_write_and_wait(xz_audio_t *thiz, uint8_t *data,
                                 uint32_t data_len)
{
    int ret;
    int try_times = 0;
    // 运行本地 4 级参量 EQ 与平滑防破音 DSP 增强
    xz_audio_dsp_process((int16_t *)data, data_len / 2);

#if PKG_XIAOZHI_USING_AEC
    uint32_t bytes;
    if (thiz->resample)
    {
        bytes = sifli_resample_process(thiz->resample, (int16_t *)data, data_len, 0);
        data = (uint8_t *)sifli_resample_get_output(thiz->resample);
        data_len = bytes;
    }
#endif

    while (!thiz->is_exit)
    {
        ret = audio_write(thiz->speaker, data, data_len);
        if (ret)
        {
            break;
        }
        rt_thread_mdelay(10);
        try_times++;
        if (try_times > 50)
        {
            LOG_I("speaker write failed len=%d\n", data_len);
            LOG_I("speaker busy, tx=%d\r\n", thiz->is_tx_enable);
            break;
        }
    }
}
static void xz_opus_thread_entry(void *p)
{
    int err;
    xz_audio_t *thiz = &xz_audio;
    thiz->decoder = opus_decoder_create(24000, 1, &err);
    RT_ASSERT(thiz->decoder);

    thiz->encoder = opus_encoder_create(16000, 1, OPUS_APPLICATION_VOIP, &err);
    RT_ASSERT(thiz->encoder);
    opus_encoder_ctl(thiz->encoder,
                     OPUS_SET_EXPERT_FRAME_DURATION(OPUS_FRAMESIZE_60_MS));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_VBR(1));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_VBR_CONSTRAINT(1));

    opus_encoder_ctl(thiz->encoder, OPUS_SET_BITRATE(32000));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_SIGNAL(OPUS_SIGNAL_VOICE));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_COMPLEXITY(5));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_LSB_DEPTH(16));

    opus_encoder_ctl(thiz->encoder, OPUS_SET_DTX(0));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_INBAND_FEC(0));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_PACKET_LOSS_PERC(0));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_PREDICTION_DISABLED(0));

    opus_encoder_ctl(thiz->encoder,
                     OPUS_SET_MAX_BANDWIDTH(OPUS_BANDWIDTH_WIDEBAND));
    opus_encoder_ctl(thiz->encoder, OPUS_SET_BANDWIDTH(OPUS_AUTO));

    opus_encoder_ctl(thiz->encoder, OPUS_SET_FORCE_MODE(MODE_SILK_ONLY));
    while (!thiz->is_exit)
    {
        rt_uint32_t evt = 0;
        rt_event_recv(thiz->event, XZ_EVENT_ALL,
                      RT_EVENT_FLAG_OR | RT_EVENT_FLAG_CLEAR,
                      RT_WAITING_FOREVER, &evt);
        if (evt & XZ_EVENT_EXIT)
        {
            break;
        }
        if ((evt & XZ_EVENT_MIC_RX) && thiz->is_rx_enable)
        {
            rt_ringbuffer_get(thiz->rb_opus_encode_input,
                              (uint8_t *)&thiz->encode_in[0], XZ_MIC_FRAME_LEN);

            opus_int32 len = opus_encode(
                thiz->encoder, (const opus_int16 *)thiz->encode_in,
                XZ_MIC_FRAME_LEN / 2, thiz->encode_out, XZ_MIC_FRAME_LEN);
            if (len < 0 || len > XZ_MIC_FRAME_LEN)
            {
                LOG_I("opus_encode len=%d samrate=%d", len,
                      g_xz_context.sample_rate);
                RT_ASSERT(0);
            }
#ifdef XIAOZHI_USING_MQTT
            xz_audio_send(thiz->encode_out, len);
#else
            xz_audio_send_using_websocket(thiz->encode_out,
                                          len); // 发送音频数据
#endif
            if (rt_ringbuffer_data_len(thiz->rb_opus_encode_input) >=
                XZ_MIC_FRAME_LEN)
            {
                rt_event_send(thiz->event, XZ_EVENT_MIC_RX);
            }
        }

        if (evt & XZ_EVENT_SPK_TX)
        {
        }

        if ((evt & XZ_EVENT_DOWNLINK) && thiz->is_tx_enable)
        {
            rt_slist_t *decode;
            rt_enter_critical();
            decode = rt_slist_first(&thiz->downlink_decode_busy);
            rt_exit_critical();
            RT_ASSERT(decode);
            xz_decode_queue_t *queue =
                rt_container_of(decode, xz_decode_queue_t, node);
            opus_int32 res = opus_decode(
                thiz->decoder, (const uint8_t *)queue->data, queue->data_len,
                (opus_int16 *)&thiz->downlink_decode_out[0], XZ_SPK_FRAME_LEN,
                0);

            if (res != XZ_SPK_FRAME_LEN / 2)
            {
                LOG_I("decode out samples=%d\n", res);
                // 解码异常时重置解码器状态防止错误累积
                if (res < 0)
                {
                    opus_decoder_ctl(thiz->decoder, OPUS_RESET_STATE);
                }
            }
            if (res > 0)
            {
                audio_write_and_wait(thiz, (uint8_t *)thiz->downlink_decode_out,
                                     res * 2);
            }

            uint8_t need_decode_gain = 0;
            rt_enter_critical();
            rt_slist_remove(&thiz->downlink_decode_busy, decode);
            rt_slist_append(&thiz->downlink_decode_idle, decode);
            if (rt_slist_first(&thiz->downlink_decode_busy))
            {
                need_decode_gain = true;
            }
            rt_exit_critical();

            if (need_decode_gain)
                rt_event_send(thiz->event, XZ_EVENT_DOWNLINK);
        }
    }
    if (thiz->encoder)
        opus_encoder_destroy(thiz->encoder);
    if (thiz->decoder)
        opus_decoder_destroy(thiz->decoder);

    rt_kprintf("---xz thread exit---\r\n");
}

void xz_aec_mic_open(xz_audio_t *thiz)
{
    if (!thiz->mic)
    {
        LOG_I("mic on,thiz->inited=%d", thiz->inited);
        // if (thiz->inited != 2)
        // {
        //     return;
        // }
        while (1)
        {
            uint8_t buf[128];
            rt_base_t level = rt_hw_interrupt_disable(); // 添加临界区保护
            int len = rt_ringbuffer_get(thiz->rb_opus_encode_input,
                                        (uint8_t *)&buf[0], sizeof(buf));
            rt_hw_interrupt_enable(level); // 恢复中断
            if (len == 0)
            {
                break;
            }
        }
        audio_parameter_t pa = {0};
        pa.write_bits_per_sample = 16;
        pa.write_channnel_num = 1;
        pa.write_samplerate = 16000;
        pa.read_bits_per_sample = 16;
        pa.read_channnel_num = 1;
        pa.read_samplerate = 16000;
        pa.read_cache_size = 0;
        pa.write_cache_size = 32000;
        pa.is_need_3a = 0;
        thiz->mic = audio_open(AUDIO_TYPE_LOCAL_MUSIC, AUDIO_TXRX, &pa,
                               mic_callback, NULL);
        RT_ASSERT(thiz->mic);
        thiz->speaker = thiz->mic;
        thiz->is_rx_enable = 1; // 麦克风常开
        thiz->is_tx_enable = 1;
    }
}
void xz_mic_open(xz_audio_t *thiz)
{
#if !PKG_XIAOZHI_USING_AEC
    if (!thiz->mic)
    {
        LOG_I("mic on");
        while (1)
        {
            uint8_t buf[128];
            int len = rt_ringbuffer_get(thiz->rb_opus_encode_input,
                                        (uint8_t *)&buf[0], sizeof(buf));
            if (len == 0)
            {
                break;
            }
        }

        audio_parameter_t pa = {0};
        pa.write_bits_per_sample = 16;
        pa.write_channnel_num = 1;
        pa.write_samplerate = 24000;
        pa.read_bits_per_sample = 16;
        pa.read_channnel_num = 1;
        pa.read_samplerate = 16000;
        pa.read_cache_size = 0;
        pa.write_cache_size = 0;
        thiz->mic = audio_open(AUDIO_TYPE_LOCAL_RECORD, AUDIO_RX, &pa,
                               mic_callback, NULL);
        RT_ASSERT(thiz->mic);
        thiz->is_rx_enable = 1;
    }
#endif
}

void xz_aec_mic_close(xz_audio_t *thiz)
{
    if (thiz->mic)
    {
        LOG_I("mic off");
        if (thiz->speaker == thiz->mic)
        {
            thiz->speaker = NULL;
        }
        audio_close(thiz->mic);
        thiz->mic = NULL;
        thiz->is_rx_enable = 0;
        if (thiz->rb_opus_encode_input)
        {
            rt_ringbuffer_reset(thiz->rb_opus_encode_input);
        }
        if (thiz->rb_vad_cache)
        {
            rt_ringbuffer_reset(thiz->rb_vad_cache);
        }
    }
}
void xz_mic_close(xz_audio_t *thiz)
{
#if !PKG_XIAOZHI_USING_AEC
    if (thiz->mic)
    {
        LOG_I("mic off");
        audio_close(thiz->mic);
        thiz->mic = NULL;
        thiz->is_rx_enable = 0;
    }
#endif
}

void xz_speaker_open(xz_audio_t *thiz)
{
#if PKG_XIAOZHI_USING_AEC
    #if STOP_SPEAKER_WHEN_DETECTED_MIC_VOICE
    LOG_I("speaker on");
    xiaozhi_ui_chat_status("\u8bb2\u8bdd\u4e2d...");
    g_xz_context.remote_sequence = 0;
    thiz->is_tx_enable = 0;
    // 重置DSP EQ滤镜状态
    for (int i = 0; i < 4; i++)
    {
        g_xz_eq[i].x1 = 0; g_xz_eq[i].x2 = 0;
        g_xz_eq[i].y1 = 0; g_xz_eq[i].y2 = 0;
    }
    // 重置Opus解码器状态，避免残留状态导致新流爆音
    if (thiz->decoder)
    {
        opus_decoder_ctl(thiz->decoder, OPUS_RESET_STATE);
    }
    // 重置重采样器状态，避免相位漂移累积
    if (thiz->resample)
    {
        sifli_resample_close(thiz->resample);
        thiz->resample = sifli_resample_open(1, 24000, 16000);
    }
    thiz->is_tx_enable = 1;
    #endif
#else
    if (!thiz->speaker)
    {
        LOG_I("speaker on,thiz->inited=%d", thiz->inited);
        // if (thiz->inited != 2)
        // {
        //     return;
        // }
        xiaozhi_ui_chat_status("\u8bb2\u8bdd\u4e2d...");
        audio_parameter_t pa = {0};
        pa.write_bits_per_sample = 16;
        pa.write_channnel_num = 1;
        pa.write_samplerate = 24000;
        pa.read_bits_per_sample = 16;
        pa.read_channnel_num = 1;
        pa.read_samplerate = 16000;
        pa.read_cache_size = 0;
        pa.write_cache_size = 32000;
        thiz->speaker =
            audio_open(AUDIO_TYPE_LOCAL_MUSIC, AUDIO_TX, &pa, NULL, NULL);
        RT_ASSERT(thiz->speaker);
        thiz->is_tx_enable = 1;
    }
#endif
}
void xz_speaker_close(xz_audio_t *thiz)
{
#if PKG_XIAOZHI_USING_AEC
    #if STOP_SPEAKER_WHEN_DETECTED_MIC_VOICE
    LOG_I("speaker off");
    xiaozhi_ui_chat_status("\u5f85\u547d\u4e2d...");
    rt_slist_t *idle;
    thiz->is_tx_enable = 0;
    rt_enter_critical();
    while (1)
    {
        idle = rt_slist_first(&thiz->downlink_decode_busy);
        if (idle)
        {
            rt_slist_remove(&thiz->downlink_decode_busy, idle);
            rt_slist_append(&thiz->downlink_decode_idle, idle);
        }
        else
        {
            break;
        }
    }
    rt_exit_critical();
    #endif
#else

    if (thiz->speaker)
    {
        for (int i = 0; i < 1000; i++)
        {
            if (!rt_slist_first(&thiz->downlink_decode_busy))
            {
                break;
            }
            rt_thread_mdelay(10);
        }
        uint32_t cache_time_ms = 150;
        audio_ioctl(thiz->speaker, 1, &cache_time_ms);
        rt_thread_mdelay(cache_time_ms + 20);
        audio_close(thiz->speaker);
        thiz->speaker = NULL;
        thiz->is_tx_enable = 0;
        rt_slist_t *idle;
        rt_enter_critical();
        while (1)
        {
            idle = rt_slist_first(&thiz->downlink_decode_busy);
            if (idle)
            {
                rt_slist_remove(&thiz->downlink_decode_busy, idle);
                rt_slist_append(&thiz->downlink_decode_idle, idle);
            }
            else
            {
                break;
            }
        }
        rt_exit_critical();
    }
#endif
}

/**
 * @brief 打开音频解码器和编码器
 *
 * 该函数负责初始化音频处理模块，包括事件创建、队列初始化、线程创建等
 * 如果模块尚未初始化，则根据参数决定是否使用WebSocket，并准备音频处理线程
 *
 * @param is_websocket 指示是否使用WebSocket的标志
 */
void xz_audio_decoder_encoder_open(uint8_t is_websocket)
{
    // 获取音频处理模块的实例
    xz_audio_t *thiz = &xz_audio;

    LOG_I("%s", XZ_AUDIO_VERSION);
    // 检查模块是否已经初始化，避免重复初始化
    if (!thiz->inited)
    {
        memset(thiz, 0, sizeof(xz_audio_t));
        // thiz->inited = 1;
#if PKG_XIAOZHI_USING_AEC
        int ret;
        thiz->vad_enabled = true;
        audio_parameter_t pa = {0};
        pa.write_bits_per_sample = 16;
        pa.write_channnel_num = 1;
        pa.write_samplerate = 16000;
        pa.read_bits_per_sample = 16;
        pa.read_channnel_num = 1;
        pa.read_samplerate = 16000;
        pa.read_cache_size = 0;
        pa.write_cache_size = 32000;
        pa.is_need_3a = 0;
        pa.disable_uplink_agc = 1;
        thiz->mic = audio_open(AUDIO_TYPE_LOCAL_MUSIC, AUDIO_TXRX, &pa,
                               mic_callback, NULL);
        RT_ASSERT(thiz->mic);

        mic_gain_decrease(4);

        thiz->speaker = thiz->mic;
        thiz->is_rx_enable = 1; // 麦克风常开
        thiz->is_tx_enable = 1;
        thiz->resample = sifli_resample_open(1, 24000, 16000);
        RT_ASSERT(thiz->resample);
        ret = WebRtcVad_Create(&thiz->handle);
        RT_ASSERT(!ret);
        ret = WebRtcVad_Init(thiz->handle);
        RT_ASSERT(!ret);
        ret = WebRtcVad_set_mode(thiz->handle, 3); // 0 ~ 3
        RT_ASSERT(!ret);

#endif
        // 根据参数设置是否使用WebSocket
        thiz->is_websocket = is_websocket;

        // 创建事件，用于音频处理中的同步
        thiz->event = rt_event_create("xzaudio", RT_IPC_FLAG_FIFO);
        RT_ASSERT(thiz->event);

        // 初始化空闲和忙状态的解码队列
        rt_slist_init(&thiz->downlink_decode_idle);
        rt_slist_init(&thiz->downlink_decode_busy);

        // 为下行链路解码队列分配内存
        for (int i = 0; i < XZ_DOWNLINK_QUEUE_NUM; i++)
        {
            thiz->downlink_queue[i].size = 512;
            thiz->downlink_queue[i].data =
                opus_heap_malloc(thiz->downlink_queue[i].size);
            RT_ASSERT(thiz->downlink_queue[i].data);

            // 将新分配的队列节点添加到空闲队列中
            rt_slist_append(&thiz->downlink_decode_idle,
                            &thiz->downlink_queue[i].node);
        }

#if PKG_XIAOZHI_USING_AEC
        thiz->rb_vad_cache = rt_ringbuffer_create(320 * VOICE_START_TIMES);
        thiz->rb_opus_encode_input = rt_ringbuffer_create(
            XZ_MIC_FRAME_LEN * 2 + 320 * VOICE_START_TIMES);
        RT_ASSERT(thiz->rb_opus_encode_input);
#else
        // 创建用于编码输入的环形缓冲区
        thiz->rb_opus_encode_input =
            rt_ringbuffer_create(XZ_MIC_FRAME_LEN * 2); // two frame
        RT_ASSERT(thiz->rb_opus_encode_input);
#endif
        // 初始化音频处理线程
        rt_err_t err;
        err = rt_thread_init(&thiz->thread, XZ_THREAD_NAME,
                             xz_opus_thread_entry, // 音频处理线程入口函数
                             NULL, g_xz_opus_stack, sizeof(g_xz_opus_stack),
                             RT_THREAD_PRIORITY_MIDDLE +
                                 RT_THREAD_PRIORITY_HIGHER,
                             RT_THREAD_TICK_DEFAULT);

        // 启动音频处理线程
        rt_thread_startup(&thiz->thread);

        // 标记模块已初始化
        thiz->inited = 1;

        rt_kprintf("xz_audio_decoder_encoder open ok\n");
    }
    rt_kprintf("xz_audio_decoder_encoder open2 ok\n");
}

void xz_audio_decoder_encoder_close(void)
{
    xz_audio_t *thiz = &xz_audio;

    LOG_I("xz_audio_decoder_encoder close in  %d", thiz->inited);

    thiz->is_exit = 1;
    rt_event_send(thiz->event, XZ_EVENT_EXIT);
    while (rt_thread_find(XZ_THREAD_NAME))
    {
        LOG_I("wait thread %s exit", XZ_THREAD_NAME);
        os_delay(100);
    }

    rt_ringbuffer_destroy(thiz->rb_opus_encode_input);
    rt_event_delete(thiz->event);

    for (int i = 0; i < XZ_DOWNLINK_QUEUE_NUM; i++)
    {
        if (thiz->downlink_queue[i].data)
        {
            opus_heap_free(thiz->downlink_queue[i].data);
            thiz->downlink_queue[i].data = NULL;
        }
    }
#if PKG_XIAOZHI_USING_AEC
    rt_ringbuffer_destroy(thiz->rb_vad_cache);
    sifli_resample_close(thiz->resample);
    audio_close(thiz->mic);
    thiz->mic = NULL;
    thiz->speaker = NULL;
    thiz->rb_vad_cache = NULL;
    thiz->resample = NULL;
    if (thiz->handle)
    {
        WebRtcVad_Free(thiz->handle);
        thiz->handle = NULL;
    }
#else
    if (thiz->mic)
    {
        audio_close(thiz->mic);
        thiz->mic = NULL;
    }

    if (thiz->speaker)
    {
        audio_close(thiz->speaker);
        thiz->speaker = NULL;
    }
#endif
    thiz->inited = 0;

    rt_kprintf("xz_audio_decoder_encoder close out ok\n");
}

void reinit_audio()
{
    xz_audio_t *thiz = &xz_audio;
    xz_aec_mic_close(thiz);
    xz_speaker_close(thiz);
    xz_audio_decoder_encoder_close();
    // 重新打开音频解码器和编码器
    xz_audio_decoder_encoder_open(1);
    xz_aec_mic_open(thiz);
    xz_speaker_open(thiz);
}

void xz_audio_downlink(uint8_t *data, uint32_t size, uint32_t *aes_value,
                       uint8_t need_aes)
{
    int try_times = 0;
    xz_audio_t *thiz = &xz_audio;
    rt_slist_t *idle;
    if (!thiz->inited)
    {
        LOG_I("%s invalid\r\n", __FUNCTION__);
        return;
    }
    // LOG_I("%s tx=%d inited=%d\r\n", __FUNCTION__, thiz->is_tx_enable,
    // thiz->inited);
    rt_enter_critical();
    idle = rt_slist_first(&thiz->downlink_decode_idle);
    if (!idle)
    {
        // 当下行队列全满时，直接回收最旧的一帧 busy 节点，不阻塞 LwIP 网络线程！
        idle = rt_slist_first(&thiz->downlink_decode_busy);
        if (idle)
        {
            rt_slist_remove(&thiz->downlink_decode_busy, idle);
        }
    }
    rt_exit_critical();

    if (idle)
    {
        xz_decode_queue_t *queue =
            rt_container_of(idle, xz_decode_queue_t, node);
        if (queue->size < size + 16)
        {
            opus_heap_free(queue->data);
            queue->size = size + 16;
            queue->data = opus_heap_malloc(queue->size);
            RT_ASSERT(queue->data);
        }
        queue->data_len = size;
        if (need_aes)
        {
            HAL_AES_init((uint32_t *)&(g_xz_context.key[0]), 16, aes_value,
                         AES_MODE_CTR);
            HAL_AES_run(AES_DEC, data, queue->data, size);
        }
        else
        {
            memcpy(queue->data, data, size);
        }
        rt_enter_critical();
        rt_slist_append(&thiz->downlink_decode_busy, idle);
        rt_exit_critical();

        rt_event_send(thiz->event, XZ_EVENT_DOWNLINK);
    }
}

/************************ (C) COPYRIGHT Sifli Technology *******END OF FILE****/
