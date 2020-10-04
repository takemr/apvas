/*
 *  BIRD -- BGP Packet Processing
 *
 *  (c) 2000 Martin Mares <mj@ucw.cz>
 *
 *  Can be freely distributed and used under the terms of the GNU GPL.
 */

#undef LOCAL_DEBUG

#include "nest/bird.h"
#include "nest/iface.h"
#include "nest/protocol.h"
#include "nest/route.h"
#include "nest/attrs.h"
#include "nest/mrtdump.h"
#include "conf/conf.h"
#include "lib/unaligned.h"
#include "lib/socket.h"

#include "nest/cli.h"

#include "bgp.h"
#include "aggsign.h"

#include <sys/time.h>
#include <stdlib.h>

#define BGP_RR_REQUEST    0
#define BGP_RR_BEGIN    1
#define BGP_RR_END    2

static struct tbf rl_rcv_update = TBF_DEFAULT_LOG_LIMITS;
static struct tbf rl_snd_update = TBF_DEFAULT_LOG_LIMITS;

struct timeval s1, t1;
int ini_time = 0;
int elasped_time = 0;
int tsum = 0;
int sumcounter = 0;


/* Table for state -> RFC 6608 FSM error subcodes */
static byte fsm_err_subcode[BS_MAX] = {
  [BS_OPENSENT] = 1,
  [BS_OPENCONFIRM] = 2,
  [BS_ESTABLISHED] = 3
};

Key key1, key2, key3, key4, key5, key6, key7, key8;

int ini_setup = 0;
int ini_sigList = 0;
int sigListCounter = 0;

typedef struct sign_m{ 
    ip_addr address;
    int pxlen;
    Sign sign;
    struct sign_m *next_ptr;
}sign_mem;

sign_mem *fst_ptr;
sign_mem *cur_ptr;
sign_mem *seach_ptr;

int allcounter = 0;
int maxcounter = 0;


void my_element_print(const String s, const Element e){
    int size = element_get_str_length(e);
    String str = (String)malloc(sizeof(char) * size);

    element_get_str(str, e);
    log("%s: %s\n", s, str);

    free(str);
}

void my_point_print(const String s, const EC_POINT p){
    int size = point_get_str_length(p);
    String str = (String)malloc(sizeof(char) * size);
    point_get_str(str, p);
    log("%s: %s\n",s, str);

    free(str);
}

void set_mpz_from_element(mpz_t z, const Element e){
    int size = element_get_str_length(e);
    String str = (String)malloc(sizeof(char) * size);
    
    element_get_str(str, e);
    mpz_set_str(z, str, 16);
    
    free(str);
}

// ********** Algorithm 1 Setup **********//
void ParaInit(){
    pairing_init(para.prg, "ECBN254a");
    point_init(para.g2, para.prg->g2);
    // ParaGenG2();
    point_set_str(para.g2, "[1462ea218754f628c4cf9127d0da02c4e5fba8cb301be2e280cc254cae726c3e 1f8af442e9acc1f28d1ed993daf21d8ec6f6e946ab013eaeaeb6108bc9ca702f,226c2b572866198b848c5ea5d1287d876cc03e6d55cc113144c5f65615144322 b1f6f6f481f353f9bfa080c7e5002333e0c1acf9ca7511c8517b0430c743214]");
    field_init(para.f, "bn254_fpa");
}

void ParaGenG2(){
    mpz_t z;
    mpz_init(z);
    mpz_set(z, para.prg->g2->cofactor);
    
    EC_POINT p;
    point_init(p, para.prg->g2);
    
    do {
        point_random(p);
        point_mul(para.g2, z, p);
    } while (point_is_infinity(para.g2) != 0);

    point_clear(p);
    mpz_clear(z);

    // my_point_print("g2", para.g2);
}

void ParaClear(){
    field_clear(para.f);
    point_clear(para.g2);
    pairing_clear(para.prg);
}

void Setup(){
    ParaInit();
}

// ********** Algorithm 2 UserKeyGen **********//
void KeyInit(Key *key){
    element_init(key->sk, para.f);
    point_init(key->pk, para.prg->g2);
}

void KeyGen(Key *key){
    //element_random(key->sk);
    // my_element_print("Privkey", key->sk);

    mpz_t tmp;
    mpz_init(tmp);
    set_mpz_from_element(tmp, key->sk);

    point_mul(key->pk, tmp, para.g2);
    //my_point_print("Pubkey", key->pk);

    mpz_clear(tmp);
}

void KeyClear(Key *key){
    point_clear(key->pk);
    element_clear(key->sk);
}

void UserKeyGen(Key *key){
    KeyInit(key);
    KeyGen(key);
}

// ********** Algorithm 3 SeqAggSign **********
void ListInit(List *list){
    for(int i = 0; i < list_size; i++) {
        point_init(list[i].pk, para.prg->g2);
        memset(list[i].m, 0x00, str_size);
    }

}

int ListLength(List *list){
    int length = 0;
    while(!point_is_infinity(list[length].pk)) {
        length++;
    }

    return length;
}

void ListAdd(List *list, const Pubkey pk, const String m){
    int length = ListLength(list);

    point_set(list[length].pk, pk);
    strcpy(list[length].m, m);
}

void ListDisplay(List *list)
{
    int length = ListLength(list);
    for(int i = 0; i < length; i++) {
        my_point_print("pk", list[i].pk);
        printf("m: %s\n", list[i].m);
    }
}

void ListClear(List *list)
{
    int length = ListLength(list);
    for(int i = 0; i < length; i++) {
        point_clear(list[i].pk);
    }
}

void HashForSign(Hash c, const Sign sign, List *list)
{
    char str[5000] = "";

    // e
    Element e;
    element_init(e, para.prg->g3);
    if(point_is_infinity(sign)) {
        element_set_one(e);
    } else {
        pairing_map(e, sign, para.g2, para.prg);
    }

    int size_e = element_get_str_length(e);
    String str_e = (String)malloc(sizeof(char) * size_e);
    element_get_str(str_e, e);
    //sprintf(str, "%s %s", str, str_e);
    sprintf(str, "%s", str_e);
    free(str_e);

    element_clear(e); 

    //ここ来る前に先にlistに自分入れてる
    for(int i = ListLength(list) - 1; i >= 0 ; i--) {
        //pk
        int size_pk = point_get_str_length(list[i].pk);
        String str_pk = (String)malloc(sizeof(char) * size_pk);
        point_get_str(str_pk, list[i].pk);
        sprintf(str, "%s %s", str, str_pk);
        free(str_pk);

        //m
        sprintf(str, "%s %s", str, list[i].m);
    }
    //printf("str: %s\n\n", str);
    point_map_to_point(c, str, strlen(str), hash_size);
}

//SeqAggSign(sign, list, &key1, "as1");
int SeqAggSign(Sign sign, List *list, const Key *key, const String m)
{
    if(ListLength(list) == 0) {
        point_init(sign, para.prg->g1);
        point_set_infinity(sign);
    }
    ListAdd(list, key->pk, m);

    EC_POINT c;
    point_init(c, para.prg->g1);
    HashForSign(c, sign, list);

    mpz_t tmp;
    mpz_init(tmp);
    set_mpz_from_element(tmp, key->sk);

    EC_POINT tmp_sign;
    point_init(tmp_sign, para.prg->g1);
    point_mul(tmp_sign, tmp, c);
    point_add(sign, sign, tmp_sign);

    point_clear(tmp_sign);
    mpz_clear(tmp);
    point_clear(c);

    //my_point_print("Sign", sign);
    //ListDisplay(list);
    //printf("\n\n\n\n");


    return 0;
}

// ********** Algorithm 5 Verify **********//
int Verify(const Sign sign, List *list)
{
    int length = ListLength(list);
   
    EC_POINT c;
    point_init(c, para.prg->g1);
    point_set_infinity(c);

    Element e;

    Element e1;
    element_init(e1, para.prg->g3);
    element_set_one(e1);
    int k;
    for(int i = 1; i <= length; i++) {//Ciを作る
        if (strchr(list[i-1].m, '/') != NULL){
          printf("reset NLRI\n");
          k = i-1; 
          element_init(e, para.prg->g3);
          element_set_one(e);
        }
        //さっき使った検証式を先頭に
        printf("平文%s\n", list[i-1].m);
        char str[5000] = "";
        // e
        int size_e = element_get_str_length(e);
        String str_e = (String)malloc(sizeof(char) * size_e);
        element_get_str(str_e, e);
        //sprintf(str, "%s %s", str, str_e);
        sprintf(str, "%s", str_e);
        free(str_e);

        
        for(int j = i - 1; j >= k; j--) {//i-1までの平文の連結（というかiまで一気に入れてる）
            //pk
            int size_pk = point_get_str_length(list[j].pk);
            String str_pk = (String)malloc(sizeof(char) * size_pk);
            point_get_str(str_pk, list[j].pk);
            sprintf(str, "%s %s", str, str_pk);
            free(str_pk);

            //m
            sprintf(str, "%s %s", str, list[j].m);
        }
        printf("str : %s\n\n", str);
        point_map_to_point(c, str, strlen(str), hash_size);//Ci=H(str)

        Element e_tmp;//右辺の掛け算
        element_init(e_tmp, para.prg->g3);
        pairing_map(e_tmp, c, list[i - 1].pk, para.prg);
        
        element_mul(e, e, e_tmp);
        element_mul(e1, e1, e_tmp);
        element_clear(e_tmp);
        
        
    }

    Element e2;//左辺
    element_init(e2, para.prg->g3);
   
    pairing_map(e2, sign, para.g2, para.prg);
    
    //my_element_print("e1", e1);
    //my_element_print("e2", e2);

    int cmp = element_cmp(e1, e2);
    element_clear(e2);
    element_clear(e1);
    element_clear(e);
    point_clear(c);

    return !cmp;
}


void initial_setup(){
    Setup(&para);
    
    KeyInit(&key1);    
    element_set_str(key1.sk, "16e5881c0994c8ed549c1f5599b5b01be13938d2ce8478b6393305bc7e1d4f64");
    KeyGen(&key1);

    KeyInit(&key2);    
    element_set_str(key2.sk, "7ba7dfdb3753cd13306bf35a1816389723c26cd4f55f9c2f9d7fae149d02c3a");
    KeyGen(&key2);

    KeyInit(&key3);    
    element_set_str(key3.sk, "19e0b7b21b22ac906d0845a72af8741d33e76072ff10bd3ed1700c1d8b7c099d");
    KeyGen(&key3);

    KeyInit(&key4);    
    element_set_str(key4.sk, "14c2884d7f63dea5712bb0d6d6bc7ff5a995ab82cd79857dff89593b3b08524");
    KeyGen(&key4);
    
    KeyInit(&key5);    
    element_set_str(key5.sk, "2e8817b39ac0d4235f88acfaa0c9486d6ec6f53eb0e035c0f6eb3ff0316789f");
    KeyGen(&key5);

    KeyInit(&key6);    
    element_set_str(key6.sk, "85f29b3cb32a14f0332458950f3b7fd8ce781015e5f02eb4b370c24316efda4");
    KeyGen(&key6);

    KeyInit(&key7);    
    element_set_str(key7.sk, "2a47df37ad51110b5878ea301d5c451d368caa293988af11f9ece6a2fd03082");
    KeyGen(&key7);

    KeyInit(&key8);    
    element_set_str(key8.sk, "1a646bbe712c4fc1cc1b4cff722149af05263c6cf76f51670028a0b58621f7aa");
    KeyGen(&key8);
}  


/*
 * MRT Dump format is not semantically specified.
 * We will use these values in appropriate fields:
 *
 * Local AS, Remote AS - configured AS numbers for given BGP instance.
 * Local IP, Remote IP - IP addresses of the TCP connection (0 if no connection)
 *
 * We dump two kinds of MRT messages: STATE_CHANGE (for BGP state
 * changes) and MESSAGE (for received BGP messages).
 *
 * STATE_CHANGE uses always AS4 variant, but MESSAGE uses AS4 variant
 * only when AS4 session is established and even in that case MESSAGE
 * does not use AS4 variant for initial OPEN message. This strange
 * behavior is here for compatibility with Quagga and Bgpdump,
 */

static byte *
mrt_put_bgp4_hdr(byte *buf, struct bgp_conn *conn, int as4)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;

  if (as4)
    {
      put_u32(buf+0, p->remote_as);
      put_u32(buf+4, p->local_as);
      buf+=8;
    }
  else
    {
      put_u16(buf+0, (p->remote_as <= 0xFFFF) ? p->remote_as : AS_TRANS);
      put_u16(buf+2, (p->local_as <= 0xFFFF)  ? p->local_as  : AS_TRANS);
      buf+=4;
    }

  put_u16(buf+0, (p->neigh && p->neigh->iface) ? p->neigh->iface->index : 0);
  put_u16(buf+2, BGP_AF);
  buf+=4;
  buf = put_ipa(buf, conn->sk ? conn->sk->daddr : IPA_NONE);
  buf = put_ipa(buf, conn->sk ? conn->sk->saddr : IPA_NONE);

  return buf;
}

static void
mrt_dump_bgp_packet(struct bgp_conn *conn, byte *pkt, unsigned len)
{
  //log("--packet--%s",__func__);
  byte *buf = alloca(128+len);  /* 128 is enough for MRT headers */
  byte *bp = buf + MRTDUMP_HDR_LENGTH;
  int as4 = conn->bgp->as4_session;

  bp = mrt_put_bgp4_hdr(bp, conn, as4);
  memcpy(bp, pkt, len);
  bp += len;
  mrt_dump_message(&conn->bgp->p, BGP4MP, as4 ? BGP4MP_MESSAGE_AS4 : BGP4MP_MESSAGE,
       buf, bp-buf);
}

static inline u16
convert_state(unsigned state)
{
  //log("--packet--%s",__func__);
  /* Convert state from our BS_* values to values used in MRTDump */
  return (state == BS_CLOSE) ? 1 : state + 1;
}

void
mrt_dump_bgp_state_change(struct bgp_conn *conn, unsigned old, unsigned new)
{
  //log("--packet--%s",__func__);
  byte buf[128];
  byte *bp = buf + MRTDUMP_HDR_LENGTH;

  bp = mrt_put_bgp4_hdr(bp, conn, 1);
  put_u16(bp+0, convert_state(old));
  put_u16(bp+2, convert_state(new));
  bp += 4;
  mrt_dump_message(&conn->bgp->p, BGP4MP, BGP4MP_STATE_CHANGE_AS4, buf, bp-buf);
}

static byte *
bgp_create_notification(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;

  BGP_TRACE(D_PACKETS, "Sending NOTIFICATION(code=%d.%d)", conn->notify_code, conn->notify_subcode);
  buf[0] = conn->notify_code;
  buf[1] = conn->notify_subcode;
  memcpy(buf+2, conn->notify_data, conn->notify_size);
  return buf + 2 + conn->notify_size;
}

#ifdef IPV6
static byte *
bgp_put_cap_ipv6(struct bgp_proto *p UNUSED, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 1;   /* Capability 1: Multiprotocol extensions */
  *buf++ = 4;   /* Capability data length */
  *buf++ = 0;   /* We support AF IPv6 */
  *buf++ = BGP_AF_IPV6;
  *buf++ = 0;   /* RFU */
  *buf++ = 1;   /* and SAFI 1 */
  return buf;
}

#else

static byte *
bgp_put_cap_ipv4(struct bgp_proto *p UNUSED, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 1;   /* Capability 1: Multiprotocol extensions */
  *buf++ = 4;   /* Capability data length */
  *buf++ = 0;   /* We support AF IPv4 */
  *buf++ = BGP_AF_IPV4;
  *buf++ = 0;   /* RFU */
  *buf++ = 1;   /* and SAFI 1 */
  return buf;
}
#endif

static byte *
bgp_put_cap_rr(struct bgp_proto *p UNUSED, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 2;   /* Capability 2: Support for route refresh */
  *buf++ = 0;   /* Capability data length */
  return buf;
}

static byte *
bgp_put_cap_ext_msg(struct bgp_proto *p UNUSED, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 6;   /* Capability 6: Support for extended messages */
  *buf++ = 0;   /* Capability data length */
  return buf;
}

static byte *
bgp_put_cap_gr1(struct bgp_proto *p, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 64;    /* Capability 64: Support for graceful restart */
  *buf++ = 6;   /* Capability data length */

  put_u16(buf, p->cf->gr_time);
  if (p->p.gr_recovery)
    buf[0] |= BGP_GRF_RESTART;
  buf += 2;

  *buf++ = 0;   /* Appropriate AF */
  *buf++ = BGP_AF;
  *buf++ = 1;   /* and SAFI 1 */
  *buf++ = p->p.gr_recovery ? BGP_GRF_FORWARDING : 0;

  return buf;
}

static byte *
bgp_put_cap_gr2(struct bgp_proto *p, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 64;    /* Capability 64: Support for graceful restart */
  *buf++ = 2;   /* Capability data length */
  put_u16(buf, 0);
  return buf + 2;
}

static byte *
bgp_put_cap_as4(struct bgp_proto *p, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 65;    /* Capability 65: Support for 4-octet AS number */
  *buf++ = 4;   /* Capability data length */
  put_u32(buf, p->local_as);
  return buf + 4;
}

static byte *
bgp_put_cap_add_path(struct bgp_proto *p, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 69;    /* Capability 69: Support for ADD-PATH */
  *buf++ = 4;   /* Capability data length */

  *buf++ = 0;   /* Appropriate AF */
  *buf++ = BGP_AF;
  *buf++ = 1;   /* SAFI 1 */

  *buf++ = p->cf->add_path;

  return buf;
}

static byte *
bgp_put_cap_err(struct bgp_proto *p UNUSED, byte *buf)
{
  //log("--packet--%s",__func__);
  *buf++ = 70;    /* Capability 70: Support for enhanced route refresh */
  *buf++ = 0;   /* Capability data length */
  return buf;
}


static byte *
bgp_create_open(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  byte *cap;
  int cap_len;

  BGP_TRACE(D_PACKETS, "Sending OPEN(ver=%d,as=%d,hold=%d,id=%08x)",
      BGP_VERSION, p->local_as, p->cf->hold_time, p->local_id);
  buf[0] = BGP_VERSION;
  put_u16(buf+1, (p->local_as < 0xFFFF) ? p->local_as : AS_TRANS);
  put_u16(buf+3, p->cf->hold_time);
  put_u32(buf+5, p->local_id);

  if (conn->start_state == BSS_CONNECT_NOCAP)
    {
      BGP_TRACE(D_PACKETS, "Skipping capabilities");
      buf[9] = 0;
      return buf + 10;
    }

  /* Skipped 3 B for length field and Capabilities parameter header */
  cap = buf + 12;

#ifndef IPV6
  if (p->cf->advertise_ipv4)
    cap = bgp_put_cap_ipv4(p, cap);
#endif

#ifdef IPV6
  cap = bgp_put_cap_ipv6(p, cap);
#endif

  if (p->cf->enable_refresh)
    cap = bgp_put_cap_rr(p, cap);

  if (p->cf->gr_mode == BGP_GR_ABLE)
    cap = bgp_put_cap_gr1(p, cap);
  else if (p->cf->gr_mode == BGP_GR_AWARE)
    cap = bgp_put_cap_gr2(p, cap);

  if (p->cf->enable_as4)
    cap = bgp_put_cap_as4(p, cap);

  if (p->cf->add_path)
    cap = bgp_put_cap_add_path(p, cap);

  if (p->cf->enable_refresh)
    cap = bgp_put_cap_err(p, cap);

  if (p->cf->enable_extended_messages)
    cap = bgp_put_cap_ext_msg(p, cap);

  cap_len = cap - buf - 12;
  if (cap_len > 0)
    {
      buf[9]  = cap_len + 2;  /* Optional params len */
      buf[10] = 2;    /* Option: Capability list */
      buf[11] = cap_len;  /* Option length */
      return cap;
    }
  else
    {
      buf[9] = 0;   /* No optional parameters */
      return buf + 10;
    }
}

static uint
bgp_encode_prefixes(struct bgp_proto *p, byte *w, struct bgp_bucket *buck, uint remains)
{
  //log("--packet--%s",__func__);
  byte *start = w;
  ip_addr a;
  int bytes;

  sigListCounter = 0;
  while (!EMPTY_LIST(buck->prefixes) && (remains >= (5+sizeof(ip_addr)+100))){
      struct bgp_prefix *px = SKIP_BACK(struct bgp_prefix, bucket_node, HEAD(buck->prefixes));
      //log("\tDequeued route %I/%d", px->n.prefix, px->n.pxlen);

      if (p->add_path_tx){
        put_u32(w, px->path_id);
        w += 4;
        remains -= 4;
      }

  
  
      List list1[list_size];
      ListInit(list1);

      char m1[str_size] = "";
      bsprintf(m1, "ski1-ski1-ski1-ski1 65001 %I/%d", px->n.prefix, px->n.pxlen);
      //log("count: %d, m1: %s", sigListCounter, m1);
      ListAdd(list1, key1.pk, m1); 

      char m2[str_size] = "";
      bsprintf(m2, "ski2-ski2-ski2-ski2 65001 65002");
      //log("count: %d, m2: %s", sigListCounter, m1);
      ListAdd(list1, key2.pk, m2); 

      char m3[str_size] = "";
      bsprintf(m3, "ski3-ski3-ski3-ski3 65001 65002 65003");
      //log("m3: %s", m3);
      ListAdd(list1, key3.pk, m3); 

      char m4[str_size] = "";
      bsprintf(m4, "ski4-ski4-ski4-ski4 65001 65002 65003 65004");
      //log("m4: %s", m4);      
      ListAdd(list1, key4.pk, m4);

      char m5[str_size] = "";
      bsprintf(m5, "ski5-ski5-ski5-ski5 65001 65002 65003 65004 65005");
      //log("m5: %s", m5);
      ListAdd(list1, key5.pk, m5);   

      char m6[str_size] = "";
      bsprintf(m6, "ski6-ski6-ski6-ski6 65001 65002 65003 65004 65005 65006");
      //log("m5: %s", m6);

      Sign sign;

      point_init(sign, para.prg->g1);

      seach_ptr = fst_ptr;
      while(1){
        if ((seach_ptr->pxlen == px->n.pxlen) && (seach_ptr->address == px->n.prefix)){
          point_set(sign, seach_ptr->sign);
          break;
        }
        seach_ptr = seach_ptr->next_ptr;
      }
      
      SeqAggSign(sign, list1, &key6, m6);
      //my_point_print("sign", sign);
      

      *w++ = px->n.pxlen; //43番目
      bytes = (px->n.pxlen + 7) / 8; //4
      a = px->n.prefix;
      ipa_hton(a);
      memcpy(w, &a, bytes);
      w += bytes;

      u8 s_bin[100];
      size_t s_bin_len = -1;
      point_to_oct(s_bin, &s_bin_len, sign);
      //log("%d, s_bin : %08u",s_bin_len, s_bin);

      memcpy(w, s_bin, s_bin_len);
      w += s_bin_len;  

      remains = remains - 70;    
      //remains -= bytes + 1;
      rem_node(&px->bucket_node);
      bgp_free_prefix(p, px);
      //log("remains: %d, w: %d---------------------", remains, w);
      // fib_delete(&p->prefix_fib, px);
      point_clear(sign);
    }
  return w - start;
}

static void
bgp_flush_prefixes(struct bgp_proto *p, struct bgp_bucket *buck)
{
  //log("--packet--%s",__func__);
  while (!EMPTY_LIST(buck->prefixes))
    {
      struct bgp_prefix *px = SKIP_BACK(struct bgp_prefix, bucket_node, HEAD(buck->prefixes));
    //  log(L_ERR "%s: - route %I/%d skipped", p->p.name, px->n.prefix, px->n.pxlen);
      rem_node(&px->bucket_node);
      bgp_free_prefix(p, px);
      // fib_delete(&p->prefix_fib, px);
    }
}

#ifndef IPV6    /* IPv4 version */

static byte *
bgp_create_update(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  struct bgp_bucket *buck;
  int remains = bgp_max_packet_length(p) - BGP_HEADER_LENGTH - 4;
  byte *w;
  int wd_size = 0;
  int r_size = 0;
  int a_size = 0;

  w = buf+2;
  if ((buck = p->withdraw_bucket) && !EMPTY_LIST(buck->prefixes))
    {
      DBG("Withdrawn routes:\n");
      wd_size = bgp_encode_prefixes(p, w, buck, remains);
      w += wd_size;
      remains -= wd_size;
    }
  put_u16(buf, wd_size);

  if (remains >= 3072)
    {
      while ((buck = (struct bgp_bucket *) HEAD(p->bucket_queue))->send_node.next)
  {
    if (EMPTY_LIST(buck->prefixes))
      {
        DBG("Deleting empty bucket %p\n", buck);
        rem_node(&buck->send_node);
        bgp_free_bucket(p, buck);
        continue;
      }

    DBG("Processing bucket %p\n", buck);
    a_size = bgp_encode_attrs(p, w+2, buck->eattrs, 2048);

    if (a_size < 0)
      {
      //  log(L_ERR "%s: Attribute list too long, skipping corresponding routes", p->p.name);
        bgp_flush_prefixes(p, buck);
        rem_node(&buck->send_node);
        bgp_free_bucket(p, buck);
        continue;
      }

    put_u16(w, a_size);
    w += a_size + 2;
    r_size = bgp_encode_prefixes(p, w, buck, remains - a_size);
    w += r_size;
    break;
  }
    }
  if (!a_size)        /* Attributes not already encoded */
    {
      put_u16(w, 0);
      w += 2;
    }
  if (wd_size || r_size)
    {
      BGP_TRACE_RL(&rl_snd_update, D_PACKETS, "Sending UPDATE");
      return w;
    }
  else
    return NULL;
}

static byte *
bgp_create_end_mark(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  BGP_TRACE(D_PACKETS, "Sending END-OF-RIB");

  put_u32(buf, 0);
  return buf+4;
}

#else   /* IPv6 version */

static inline int
same_iface(struct bgp_proto *p, ip_addr *ip)
{
  //log("--packet--%s",__func__);
  neighbor *n = neigh_find(&p->p, ip, 0);
  return n && p->neigh && n->iface == p->neigh->iface;
}

static byte *
bgp_create_update(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  struct bgp_bucket *buck;
  int size, second, rem_stored;
  int remains = bgp_max_packet_length(p) - BGP_HEADER_LENGTH - 4;
  byte *w, *w_stored, *tmp, *tstart;
  ip_addr *ipp, ip, ip_ll;
  ea_list *ea;
  eattr *nh;

  put_u16(buf, 0);
  w = buf+4;

  if ((buck = p->withdraw_bucket) && !EMPTY_LIST(buck->prefixes))
    {
      DBG("Withdrawn routes:\n");
      tmp = bgp_attach_attr_wa(&ea, bgp_linpool, BA_MP_UNREACH_NLRI, remains-8);
      *tmp++ = 0;
      *tmp++ = BGP_AF_IPV6;
      *tmp++ = 1;
      ea->attrs[0].u.ptr->length = 3 + bgp_encode_prefixes(p, tmp, buck, remains-11);
      size = bgp_encode_attrs(p, w, ea, remains);
      ASSERT(size >= 0);
      w += size;
      remains -= size;
    }

  if (remains >= 3072)
    {
      while ((buck = (struct bgp_bucket *) HEAD(p->bucket_queue))->send_node.next)
  {
    if (EMPTY_LIST(buck->prefixes))
      {
        DBG("Deleting empty bucket %p\n", buck);
        rem_node(&buck->send_node);
        bgp_free_bucket(p, buck);
        continue;
      }

    DBG("Processing bucket %p\n", buck);
    rem_stored = remains;
    w_stored = w;

    size = bgp_encode_attrs(p, w, buck->eattrs, 2048);
    if (size < 0)
      {
    //    log(L_ERR "%s: Attribute list too long, skipping corresponding routes", p->p.name);
        bgp_flush_prefixes(p, buck);
        rem_node(&buck->send_node);
        bgp_free_bucket(p, buck);
        continue;
      }
    w += size;
    remains -= size;

    /* We have two addresses here in NEXT_HOP eattr. Really.
       Unless NEXT_HOP was modified by filter */
    nh = ea_find(buck->eattrs, EA_CODE(EAP_BGP, BA_NEXT_HOP));
    ASSERT(nh);
    second = (nh->u.ptr->length == NEXT_HOP_LENGTH);
    ipp = (ip_addr *) nh->u.ptr->data;
    ip = ipp[0];
    ip_ll = IPA_NONE;

    if (ipa_equal(ip, p->source_addr))
      ip_ll = p->local_link;
    else
      {
        /* If we send a route with 'third party' next hop destinated 
         * in the same interface, we should also send a link local 
         * next hop address. We use the received one (stored in the 
         * other part of BA_NEXT_HOP eattr). If we didn't received
         * it (for example it is a static route), we can't use
         * 'third party' next hop and we have to use local IP address
         * as next hop. Sending original next hop address without
         * link local address seems to be a natural way to solve that
         * problem, but it is contrary to RFC 2545 and Quagga does not
         * accept such routes.
         *
         * There are two cases, either we have global IP, or
         * IPA_NONE if the neighbor is link-local. For IPA_NONE,
         * we suppose it is on the same iface, see bgp_update_attrs().
         */

        if (ipa_zero(ip) || same_iface(p, &ip))
    {
      if (second && ipa_nonzero(ipp[1]))
        ip_ll = ipp[1];
      else
        {
          switch (p->cf->missing_lladdr)
      {
      case MLL_SELF:
        ip = p->source_addr;
        ip_ll = p->local_link;
        break;
      case MLL_DROP:
      //  log(L_ERR "%s: Missing link-local next hop address, skipping corresponding routes", p->p.name);
        w = w_stored;
        remains = rem_stored;
        bgp_flush_prefixes(p, buck);
        rem_node(&buck->send_node);
        bgp_free_bucket(p, buck);
        continue;
      case MLL_IGNORE:
        break;
      }
        }
    }
      }

    tstart = tmp = bgp_attach_attr_wa(&ea, bgp_linpool, BA_MP_REACH_NLRI, remains-8);
    *tmp++ = 0;
    *tmp++ = BGP_AF_IPV6;
    *tmp++ = 1;

    if (ipa_is_link_local(ip))
      ip = IPA_NONE;

    if (ipa_nonzero(ip_ll))
      {
        *tmp++ = 32;
        ipa_hton(ip);
        memcpy(tmp, &ip, 16);
        ipa_hton(ip_ll);
        memcpy(tmp+16, &ip_ll, 16);
        tmp += 32;
      }
    else
      {
        *tmp++ = 16;
        ipa_hton(ip);
        memcpy(tmp, &ip, 16);
        tmp += 16;
      }

    *tmp++ = 0;     /* No SNPA information */
    tmp += bgp_encode_prefixes(p, tmp, buck, remains - (8+3+32+1));
    ea->attrs[0].u.ptr->length = tmp - tstart;
    size = bgp_encode_attrs(p, w, ea, remains);
    ASSERT(size >= 0);
    w += size;
    break;
  }
    }

  size = w - (buf+4);
  put_u16(buf+2, size);
  lp_flush(bgp_linpool);
  if (size)
    {
      BGP_TRACE_RL(&rl_snd_update, D_PACKETS, "Sending UPDATE");
      return w;
    }
  else
    return NULL;
}

static byte *
bgp_create_end_mark(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  BGP_TRACE(D_PACKETS, "Sending END-OF-RIB");

  put_u16(buf+0, 0);
  put_u16(buf+2, 6);  /* length 4-9 */
  buf += 4;

  /* Empty MP_UNREACH_NLRI atribute */
  *buf++ = BAF_OPTIONAL;
  *buf++ = BA_MP_UNREACH_NLRI;
  *buf++ = 3;   /* Length 7-9 */
  *buf++ = 0;   /* AFI */
  *buf++ = BGP_AF_IPV6;
  *buf++ = 1;   /* SAFI */
  return buf;
}

#endif

static inline byte *
bgp_create_route_refresh(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  BGP_TRACE(D_PACKETS, "Sending ROUTE-REFRESH");

  /* Original original route refresh request, RFC 2918 */
  *buf++ = 0;
  *buf++ = BGP_AF;
  *buf++ = BGP_RR_REQUEST;
  *buf++ = 1;   /* SAFI */
  return buf;
}

static inline byte *
bgp_create_begin_refresh(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  BGP_TRACE(D_PACKETS, "Sending BEGIN-OF-RR");

  /* Demarcation of beginning of route refresh (BoRR), RFC 7313 */
  *buf++ = 0;
  *buf++ = BGP_AF;
  *buf++ = BGP_RR_BEGIN;
  *buf++ = 1;   /* SAFI */
  return buf;
}

static inline byte *
bgp_create_end_refresh(struct bgp_conn *conn, byte *buf)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  BGP_TRACE(D_PACKETS, "Sending END-OF-RR");

  /* Demarcation of ending of route refresh (EoRR), RFC 7313 */
  *buf++ = 0;
  *buf++ = BGP_AF;
  *buf++ = BGP_RR_END;
  *buf++ = 1;   /* SAFI */
  return buf;
}


static void
bgp_create_header(byte *buf, uint len, uint type)
{
  //log("--packet--%s",__func__);
  memset(buf, 0xff, 16);    /* Marker */
  put_u16(buf+16, len);
  buf[18] = type;
}

/**
 * bgp_fire_tx - transmit packets
 * @conn: connection
 *
 * Whenever the transmit buffers of the underlying TCP connection
 * are free and we have any packets queued for sending, the socket functions
 * call bgp_fire_tx() which takes care of selecting the highest priority packet
 * queued (Notification > Keepalive > Open > Update), assembling its header
 * and body and sending it to the connection.
 */
static int
bgp_fire_tx(struct bgp_conn *conn)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  uint s = conn->packets_to_send;
  sock *sk = conn->sk;
  byte *buf, *pkt, *end;
  int type;

  if (!sk)
    {
      conn->packets_to_send = 0;
      return 0;
    }
  buf = sk->tbuf;
  pkt = buf + BGP_HEADER_LENGTH;

  if (s & (1 << PKT_SCHEDULE_CLOSE))
    {
      /* We can finally close connection and enter idle state */
      bgp_conn_enter_idle_state(conn);
      return 0;
    }
  if (s & (1 << PKT_NOTIFICATION))
    {
      s = 1 << PKT_SCHEDULE_CLOSE;
      type = PKT_NOTIFICATION;
      end = bgp_create_notification(conn, pkt);
    }
  else if (s & (1 << PKT_KEEPALIVE))
    {
      s &= ~(1 << PKT_KEEPALIVE);
      type = PKT_KEEPALIVE;
      end = pkt;      /* Keepalives carry no data */
      BGP_TRACE(D_PACKETS, "Sending KEEPALIVE");
      bgp_start_timer(conn->keepalive_timer, conn->keepalive_time);
    }
  else if (s & (1 << PKT_OPEN))
    {
      s &= ~(1 << PKT_OPEN);
      type = PKT_OPEN;
      end = bgp_create_open(conn, pkt);
    }
  else if (s & (1 << PKT_ROUTE_REFRESH))
    {
      s &= ~(1 << PKT_ROUTE_REFRESH);
      type = PKT_ROUTE_REFRESH;
      end = bgp_create_route_refresh(conn, pkt);
    }
  else if (s & (1 << PKT_BEGIN_REFRESH))
    {
      s &= ~(1 << PKT_BEGIN_REFRESH);
      type = PKT_ROUTE_REFRESH; /* BoRR is a subtype of RR */
      end = bgp_create_begin_refresh(conn, pkt);
    }
  else if (s & (1 << PKT_UPDATE))
    {
      type = PKT_UPDATE;
      end = bgp_create_update(conn, pkt);

      if (!end)
        {
    /* No update to send, perhaps we need to send End-of-RIB or EoRR */

    conn->packets_to_send = 0;

    if (p->feed_state == BFS_LOADED)
    {
      type = PKT_UPDATE;
      end = bgp_create_end_mark(conn, pkt);
    }

    else if (p->feed_state == BFS_REFRESHED)
    {
      type = PKT_ROUTE_REFRESH;
      end = bgp_create_end_refresh(conn, pkt);
    }

    else /* Really nothing to send */
      return 0;

    p->feed_state = BFS_NONE;
  }
    }
  else
    return 0;

  conn->packets_to_send = s;
  bgp_create_header(buf, end - buf, type);
  return sk_send(sk, end - buf);
}

/**
 * bgp_schedule_packet - schedule a packet for transmission
 * @conn: connection
 * @type: packet type
 *
 * Schedule a packet of type @type to be sent as soon as possible.
 */
void
bgp_schedule_packet(struct bgp_conn *conn, int type)
{
  //log("--packet--%s",__func__);
  DBG("BGP: Scheduling packet type %d\n", type);
  conn->packets_to_send |= 1 << type;
  if (conn->sk && conn->sk->tpos == conn->sk->tbuf && !ev_active(conn->tx_ev))
    ev_schedule(conn->tx_ev);
}

void
bgp_kick_tx(void *vconn)
{
  //log("--packet--%s",__func__);
  struct bgp_conn *conn = vconn;

  DBG("BGP: kicking TX\n");
  while (bgp_fire_tx(conn) > 0)
    ;
}

void
bgp_tx(sock *sk)
{
  //log("--packet--%s",__func__);
  struct bgp_conn *conn = sk->data;

  DBG("BGP: TX hook\n");
  while (bgp_fire_tx(conn) > 0)
    ;
}

/* Capatibility negotiation as per RFC 2842 */

void
bgp_parse_capabilities(struct bgp_conn *conn, byte *opt, int len)
{
  //log("--packet--%s",__func__);
  // struct bgp_proto *p = conn->bgp;
  int i, cl;

  while (len > 0)
    {
      if (len < 2 || len < 2 + opt[1])
  goto err;

      cl = opt[1];

      switch (opt[0])
  {
  case 2: /* Route refresh capability, RFC 2918 */
    if (cl != 0)
      goto err;
    conn->peer_refresh_support = 1;
    break;

  case 6: /* Extended message length capability, draft */
    if (cl != 0)
      goto err;
    conn->peer_ext_messages_support = 1;
    break;

  case 64: /* Graceful restart capability, RFC 4724 */
    if (cl % 4 != 2)
      goto err;
    conn->peer_gr_aware = 1;
    conn->peer_gr_able = 0;
    conn->peer_gr_time = get_u16(opt + 2) & 0x0fff;
    conn->peer_gr_flags = opt[2] & 0xf0;
    conn->peer_gr_aflags = 0;
    for (i = 2; i < cl; i += 4)
      if (opt[2+i+0] == 0 && opt[2+i+1] == BGP_AF && opt[2+i+2] == 1) /* Match AFI/SAFI */
        {
    conn->peer_gr_able = 1;
    conn->peer_gr_aflags = opt[2+i+3];
        }
    break;

  case 65: /* AS4 capability, RFC 4893 */
    if (cl != 4)
      goto err;
    conn->peer_as4_support = 1;
    if (conn->bgp->cf->enable_as4)
      conn->advertised_as = get_u32(opt + 2);
    break;

  case 69: /* ADD-PATH capability, draft */
    if (cl % 4)
      goto err;
    for (i = 0; i < cl; i += 4)
      if (opt[2+i+0] == 0 && opt[2+i+1] == BGP_AF && opt[2+i+2] == 1) /* Match AFI/SAFI */
        conn->peer_add_path = opt[2+i+3];
    if (conn->peer_add_path > ADD_PATH_FULL)
      goto err;
    break;

  case 70: /* Enhanced route refresh capability, RFC 7313 */
    if (cl != 0)
      goto err;
    conn->peer_enhanced_refresh_support = 1;
    break;

    /* We can safely ignore all other capabilities */
  }
      len -= 2 + cl;
      opt += 2 + cl;
    }
  return;

 err:
  bgp_error(conn, 2, 0, NULL, 0);
  return;
}

static int
bgp_parse_options(struct bgp_conn *conn, byte *opt, int len)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  int ol;

  while (len > 0)
    {
      if (len < 2 || len < 2 + opt[1])
  { bgp_error(conn, 2, 0, NULL, 0); return 0; }
#ifdef LOCAL_DEBUG
      {
  int i;
  DBG("\tOption %02x:", opt[0]);
  for(i=0; i<opt[1]; i++)
    DBG(" %02x", opt[2+i]);
  DBG("\n");
      }
#endif

      ol = opt[1];
      switch (opt[0])
  {
  case 2:
    if (conn->start_state == BSS_CONNECT_NOCAP)
      BGP_TRACE(D_PACKETS, "Ignoring received capabilities");
    else
      bgp_parse_capabilities(conn, opt + 2, ol);
    break;

  default:
    /*
     *  BGP specs don't tell us to send which option
     *  we didn't recognize, but it's common practice
     *  to do so. Also, capability negotiation with
     *  Cisco routers doesn't work without that.
     */
    bgp_error(conn, 2, 4, opt, ol);
    return 0;
  }
      len -= 2 + ol;
      opt += 2 + ol;
    }
  return 0;
}

static void
bgp_rx_open(struct bgp_conn *conn, byte *pkt, int len)
{
  //log("--packet--%s",__func__);
  struct bgp_conn *other;
  struct bgp_proto *p = conn->bgp;
  unsigned hold;
  u16 base_as;
  u32 id;

  /* Check state */
  if (conn->state != BS_OPENSENT)
    { bgp_error(conn, 5, fsm_err_subcode[conn->state], NULL, 0); return; }

  /* Check message contents */
  if (len < 29 || len != 29 + pkt[28])
    { bgp_error(conn, 1, 2, pkt+16, 2); return; }
  if (pkt[19] != BGP_VERSION)
    { bgp_error(conn, 2, 1, pkt+19, 1); return; } /* RFC 1771 says 16 bits, draft-09 tells to use 8 */
  conn->advertised_as = base_as = get_u16(pkt+20);
  hold = get_u16(pkt+22);
  id = get_u32(pkt+24);
  BGP_TRACE(D_PACKETS, "Got OPEN(as=%d,hold=%d,id=%08x)", conn->advertised_as, hold, id);

  if (bgp_parse_options(conn, pkt+29, pkt[28]))
    return;

  if (hold > 0 && hold < 3)
    { bgp_error(conn, 2, 6, pkt+22, 2); return; }

  /* RFC 6286 2.2 - router ID is nonzero and AS-wide unique */
  if (!id || (p->is_internal && id == p->local_id))
    { bgp_error(conn, 2, 3, pkt+24, -4); return; }

  if ((conn->advertised_as != base_as) && (base_as != AS_TRANS))
    log(L_WARN "%s: Peer advertised inconsistent AS numbers", p->p.name);

  if (conn->advertised_as != p->remote_as)
    {
      if (conn->peer_as4_support)
  {
    u32 val = htonl(conn->advertised_as);
    bgp_error(conn, 2, 2, (byte *) &val, 4);
  }
      else
  bgp_error(conn, 2, 2, pkt+20, 2);

      return;
    }

  /* Check the other connection */
  other = (conn == &p->outgoing_conn) ? &p->incoming_conn : &p->outgoing_conn;
  switch (other->state)
    {
    case BS_CONNECT:
    case BS_ACTIVE:
      /* Stop outgoing connection attempts */
      bgp_conn_enter_idle_state(other);
      break;

    case BS_IDLE:
    case BS_OPENSENT:
    case BS_CLOSE:
      break;

    case BS_OPENCONFIRM:
      /*
       * Description of collision detection rules in RFC 4271 is confusing and
       * contradictory, but it is essentially:
       *
       * 1. Router with higher ID is dominant
       * 2. If both have the same ID, router with higher ASN is dominant [RFC6286]
       * 3. When both connections are in OpenConfirm state, one initiated by
       *    the dominant router is kept.
       *
       * The first line in the expression below evaluates whether the neighbor
       * is dominant, the second line whether the new connection was initiated
       * by the neighbor. If both are true (or both are false), we keep the new
       * connection, otherwise we keep the old one.
       */
      if (((p->local_id < id) || ((p->local_id == id) && (p->local_as < p->remote_as)))
    == (conn == &p->incoming_conn))
        {
    /* Should close the other connection */
    BGP_TRACE(D_EVENTS, "Connection collision, giving up the other connection");
    bgp_error(other, 6, 7, NULL, 0);
    break;
  }
      /* Fall thru */
    case BS_ESTABLISHED:
      /* Should close this connection */
      BGP_TRACE(D_EVENTS, "Connection collision, giving up this connection");
      bgp_error(conn, 6, 7, NULL, 0);
      return;
    default:
      bug("bgp_rx_open: Unknown state");
    }

  /* Update our local variables */
  conn->hold_time = MIN(hold, p->cf->hold_time);
  conn->keepalive_time = p->cf->keepalive_time ? : conn->hold_time / 3;
  p->remote_id = id;
  p->as4_session = p->cf->enable_as4 && conn->peer_as4_support;
  p->add_path_rx = (p->cf->add_path & ADD_PATH_RX) && (conn->peer_add_path & ADD_PATH_TX);
  p->add_path_tx = (p->cf->add_path & ADD_PATH_TX) && (conn->peer_add_path & ADD_PATH_RX);
  p->gr_ready = p->cf->gr_mode && conn->peer_gr_able;
  p->ext_messages = p->cf->enable_extended_messages && conn->peer_ext_messages_support;

  if (p->add_path_tx)
    p->p.accept_ra_types = RA_ANY;

  DBG("BGP: Hold timer set to %d, keepalive to %d, AS to %d, ID to %x, AS4 session to %d\n", conn->hold_time, conn->keepalive_time, p->remote_as, p->remote_id, p->as4_session);

  bgp_schedule_packet(conn, PKT_KEEPALIVE);
  bgp_start_timer(conn->hold_timer, conn->hold_time);
  bgp_conn_enter_openconfirm_state(conn);
}


static inline void
bgp_rx_end_mark(struct bgp_proto *p)
{
  //log("--packet--%s",__func__);
  BGP_TRACE(D_PACKETS, "Got END-OF-RIB");

  if (p->load_state == BFS_LOADING)
    p->load_state = BFS_NONE;

  if (p->p.gr_recovery)
    proto_graceful_restart_unlock(&p->p);

  if (p->gr_active)
    bgp_graceful_restart_done(p);
}


#define DECODE_PREFIX(pp, ll) do {    \
  if (p->add_path_rx)       \
  {           \
    if (ll < 5) { err=1; goto done; }   \
    path_id = get_u32(pp);      \
    pp += 4;          \
    ll -= 4;          \
  }           \
  int b = *pp++;        \
  int q;          \
  ll--;           \
  if (b > BITS_PER_IP_ADDRESS) { err=10; goto done; } \
  q = (b+7) / 8;        \
  if (ll < q) { err=1; goto done; }   \
  memcpy(&prefix, pp, q);     \
  pp += q;          \
  ll -= q;          \
  ipa_ntoh(prefix);       \
  prefix = ipa_and(prefix, ipa_mkmask(b));  \
  pxlen = b;          \
} while (0)


static inline void
bgp_rte_update(struct bgp_proto *p, ip_addr prefix, int pxlen,
         u32 path_id, u32 *last_id, struct rte_src **src,
         rta *a0, rta **a)
{
  //log("--packet--%s",__func__);
  if (path_id != *last_id)
    {
      *src = rt_get_source(&p->p, path_id);
      *last_id = path_id;

      if (*a)
  {
    rta_free(*a);
    *a = NULL;
  }
    }

  /* Prepare cached route attributes */
  if (!*a)
    {
      a0->src = *src;

      /* Workaround for rta_lookup() breaking eattrs */
      ea_list *ea = a0->eattrs;
      *a = rta_lookup(a0);
      a0->eattrs = ea;
    }

  net *n = net_get(p->p.table, prefix, pxlen);
  rte *e = rte_get_temp(rta_clone(*a));
  e->net = n;
  e->pflags = 0;
  e->u.bgp.suppressed = 0;
  rte_update2(p->p.main_ahook, n, e, *src);
}

static inline void
bgp_rte_withdraw(struct bgp_proto *p, ip_addr prefix, int pxlen,
     u32 path_id, u32 *last_id, struct rte_src **src)
{
  log("--packet--%s",__func__);
  if (path_id != *last_id)
    {
      *src = rt_find_source(&p->p, path_id);
      *last_id = path_id;
    }

  net *n = net_find(p->p.table, prefix, pxlen);
  rte_update2( p->p.main_ahook, n, NULL, *src);
}

static inline int
bgp_set_next_hop(struct bgp_proto *p, rta *a)
{
  //log("--packet--%s",__func__);
  struct eattr *nh = ea_find(a->eattrs, EA_CODE(EAP_BGP, BA_NEXT_HOP));
  ip_addr *nexthop = (ip_addr *) nh->u.ptr->data;

#ifdef IPV6
  int second = (nh->u.ptr->length == NEXT_HOP_LENGTH) && ipa_nonzero(nexthop[1]);

  /* First address should not be link-local, but may be zero in direct mode */
  if (ipa_is_link_local(*nexthop))
    *nexthop = IPA_NONE;
#else
  int second = 0;
#endif

  if (p->cf->gw_mode == GW_DIRECT)
    {
      neighbor *ng = NULL;

      if (ipa_nonzero(*nexthop))
  ng = neigh_find(&p->p, nexthop, 0);
      else if (second)  /* GW_DIRECT -> single_hop -> p->neigh != NULL */
  ng = neigh_find2(&p->p, nexthop + 1, p->neigh->iface, 0);

      /* Fallback */
      if (!ng)
  ng = p->neigh;

      if (ng->scope == SCOPE_HOST)
  return 0;

      a->dest = RTD_ROUTER;
      a->gw = ng->addr;
      a->iface = ng->iface;
      a->hostentry = NULL;
      a->igp_metric = 0;
    }
  else /* GW_RECURSIVE */
    {
      if (ipa_zero(*nexthop))
    return 0;

      rta_set_recursive_next_hop(p->p.table, a, p->igp_table, nexthop, nexthop + second);
    }

  return 1;
}

#ifndef IPV6    /* IPv4 version */

static void
bgp_do_rx_update(struct bgp_conn *conn,
     byte *withdrawn, int withdrawn_len,
     byte *nlri, int nlri_len,
     byte *attrs, int attr_len)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  struct rte_src *src = p->p.main_source;
  rta *a0, *a = NULL;
  ip_addr prefix;
  int pxlen, err = 0;
  u32 path_id = 0;
  u32 last_id = 0;

  if (!ini_setup){
    initial_setup();
    ini_setup = 1;
    fst_ptr = (sign_mem*)malloc(sizeof(sign_mem));
    fst_ptr->next_ptr = NULL;    
  }

  /* Check for End-of-RIB marker */
  if (!withdrawn_len && !attr_len && !nlri_len)
    {
      bgp_rx_end_mark(p);
      return;
    }

  /* Withdraw routes */
  while (withdrawn_len)
    {
      DECODE_PREFIX(withdrawn, withdrawn_len);
      DBG("Withdraw %I/%d\n", prefix, pxlen);

      bgp_rte_withdraw(p, prefix, pxlen, path_id, &last_id, &src);
    }

  if (!attr_len && !nlri_len)       /* shortcut */
    return;

  a0 = bgp_decode_attrs(conn, attrs, attr_len, bgp_linpool, nlri_len);

  if (conn->state != BS_ESTABLISHED)    /* fatal error during decoding */
    return;

  if (a0 && nlri_len && !bgp_set_next_hop(p, a0))
    a0 = NULL;

  last_id = 0;
  src = p->p.main_source;

  char sign_str[170];
  int i = 0;
  char perleft = '[';
  char comma =  ',';
  char perright = ']';
  List list1[list_size];
  //int sigListCounter = 0;

  nlri += 100;
  nlri_len -= 100;

  while (nlri_len)
    {     
      DECODE_PREFIX(nlri, nlri_len);
      
      sign_str[0]='\0';
    
      bsprintf(sign_str, "%c", perleft);
    
      bsprintf(sign_str, "%s%x", sign_str, (*(nlri+1)));
    
      for (i = 2; i <= 32; ++i){
        //log("%d", *(nlri+i));
        if (((int)(*(nlri+i)))<16){
          bsprintf(sign_str, "%s0%x", sign_str, (*(nlri+i)));
        }else{
          bsprintf(sign_str, "%s%x", sign_str, (*(nlri+i)));
        }        
        //log("sign_str: %s", sign_str);
      }

      bsprintf(sign_str, "%s%c", sign_str, comma);
      //log("sign_str: %s", sign_str);

      bsprintf(sign_str, "%s%x", sign_str, (*(nlri+33)));
      //log("sign_str: %s", sign_str);

      for (i = 34; i <= 64; ++i){
        //log("%d", *(nlri+i));
        if (((int)(*(nlri+i)))<16){
          bsprintf(sign_str, "%s0%x", sign_str, (*(nlri+i)));
        }else{
          bsprintf(sign_str, "%s%x", sign_str, (*(nlri+i)));
        }
        //log("sign_str: %s", sign_str);        
      }
      
      bsprintf(sign_str, "%s%c", sign_str, perright);
      //log("sign_str: %s", sign_str);

      Sign sign_tmp;
      point_init(sign_tmp, para.prg->g1);

      point_set_str(sign_tmp, sign_str);

      //my_point_print("sign_tmp", sign_tmp);

    
      //検証(AS6)
      ListInit(list1);
      char m1[str_size] = "";
      bsprintf(m1, "ski1-ski1-ski1-ski1 65001 %I/%d", prefix, pxlen);
      //log("m1: %s", m1);
      ListAdd(list1, key1.pk, m1);

      char m2[str_size] = "";
      bsprintf(m2, "ski2-ski2-ski2-ski2 65001 65002");
      //log("m2: %s", m2);
      ListAdd(list1, key2.pk, m2);

      char m3[str_size] = "";
      bsprintf(m3, "ski3-ski3-ski3-ski3 65001 65002 65003");
      //log("m3: %s", m3);
      ListAdd(list1, key3.pk, m3); 

      char m4[str_size] = "";
      bsprintf(m4, "ski4-ski4-ski4-ski4 65001 65002 65003 65004");
      //log("m4: %s", m4);
      ListAdd(list1, key4.pk, m4);       

      char m5[str_size] = "";
      bsprintf(m5, "ski5-ski5-ski5-ski5 65001 65002 65003 65004 65005");
      //log("m5: %s", m5);
      ListAdd(list1, key5.pk, m5);       



     Verify(sign_tmp, list1);
      //log("VERIFY6 %d", Verify(sign_tmp, list1));

      sign_mem *new_sign = (sign_mem*)malloc(sizeof(sign_mem));
      point_init(new_sign->sign, para.prg->g1);
      point_set(new_sign->sign, sign_tmp);
      new_sign->address = prefix;
      new_sign->pxlen = pxlen;

      point_clear(sign_tmp);

      if (fst_ptr->next_ptr == NULL){
        fst_ptr->next_ptr = new_sign;
        cur_ptr = new_sign;
      }else{
        cur_ptr->next_ptr = new_sign;
        cur_ptr = new_sign;
      }

       if (allcounter == 0){
            gettimeofday(&s1, NULL);
        }
      allcounter++;
   if (allcounter%1000 == 0){
      
        gettimeofday(&t1, NULL);
        //log("timeEnd: %d", t1.tv_sec);
        //log("countAll: %d, time: %d", allcounter, (t1.tv_sec - s1.tv_sec));
        elasped_time = t1.tv_sec - s1.tv_sec;
            tsum = tsum + elasped_time;
            sumcounter++;
            log("count: %d, time: %d, ave: %d", allcounter, elasped_time, tsum/sumcounter); 
        gettimeofday(&s1, NULL);
        //log("timeStart: %d", s1.tv_sec);        
      }

      nlri += 65;
      nlri_len -= 65;
      //log("**nlri: %u, nlri_len:%d", nlri, nlri_len);
      if (a0)
        bgp_rte_update(p, prefix, pxlen, path_id, &last_id, &src, a0, &a);
      else /* Forced withdraw as a result of soft error */
        bgp_rte_withdraw(p, prefix, pxlen, path_id, &last_id, &src);

      //log("***nlri: %u, nlri_len:%d", nlri, nlri_len);
    }
    //for (int i = 0; i < 10000; ++i)
    //{
    //    log("sigList[%d]:", i);
    //    my_point_print(":", sigList[i]);
    //}
    //ini_sigList = 0;

 done:
  if (a)
    rta_free(a);

  if (err)
    bgp_error(conn, 3, err, NULL, 0);

  return;

}

#else     /* IPv6 version */

#define DO_NLRI(name)         \
  start = x = p->name##_start;        \
  len = len0 = p->name##_len;       \
  if (len)            \
    {             \
      if (len < 3) { err=9; goto done; }    \
      af = get_u16(x);          \
      sub = x[2];         \
      x += 3;           \
      len -= 3;           \
      DBG("\tNLRI AF=%d sub=%d len=%d\n", af, sub, len);\
    }             \
  else              \
    af = 0;           \
  if (af == BGP_AF_IPV6)

static void
bgp_attach_next_hop(rta *a0, byte *x)
{
  //log("--packet--%s",__func__);
  ip_addr *nh = (ip_addr *) bgp_attach_attr_wa(&a0->eattrs, bgp_linpool, BA_NEXT_HOP, NEXT_HOP_LENGTH);
  memcpy(nh, x+1, 16);
  ipa_ntoh(nh[0]);

  /* We store received link local address in the other part of BA_NEXT_HOP eattr. */
  if (*x == 32)
    {
      memcpy(nh+1, x+17, 16);
      ipa_ntoh(nh[1]);
    }
  else
    nh[1] = IPA_NONE;
}


static void
bgp_do_rx_update(struct bgp_conn *conn,
     byte *withdrawn, int withdrawn_len,
     byte *nlri, int nlri_len,
     byte *attrs, int attr_len)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  struct rte_src *src = p->p.main_source;
  byte *start, *x;
  int len, len0;
  unsigned af, sub;
  rta *a0, *a = NULL;
  ip_addr prefix;
  int pxlen, err = 0;
  u32 path_id = 0;
  u32 last_id = 0;

  p->mp_reach_len = 0;
  p->mp_unreach_len = 0;
  a0 = bgp_decode_attrs(conn, attrs, attr_len, bgp_linpool, 0);

  if (conn->state != BS_ESTABLISHED)  /* fatal error during decoding */
    return;

  /* Check for End-of-RIB marker */
  if ((attr_len < 8) && !withdrawn_len && !nlri_len && !p->mp_reach_len &&
      (p->mp_unreach_len == 3) && (get_u16(p->mp_unreach_start) == BGP_AF_IPV6))
    {
      bgp_rx_end_mark(p);
      return;
    }

  DO_NLRI(mp_unreach)
    {
      while (len)
  {
    DECODE_PREFIX(x, len);
    DBG("Withdraw %I/%d\n", prefix, pxlen);
    bgp_rte_withdraw(p, prefix, pxlen, path_id, &last_id, &src);
  }
    }

  DO_NLRI(mp_reach)
    {
      /* Create fake NEXT_HOP attribute */
      if (len < 1 || (*x != 16 && *x != 32) || len < *x + 2)
  { err = 9; goto done; }

      if (a0)
  bgp_attach_next_hop(a0, x);

      /* Also ignore one reserved byte */
      len -= *x + 2;
      x += *x + 2;

      if (a0 && ! bgp_set_next_hop(p, a0))
  a0 = NULL;

      last_id = 0;
      src = p->p.main_source;

      while (len)
  {
    DECODE_PREFIX(x, len);
    DBG("Add %I/%d\n", prefix, pxlen);

    if (a0)
      bgp_rte_update(p, prefix, pxlen, path_id, &last_id, &src, a0, &a);
    else /* Forced withdraw as a result of soft error */
      bgp_rte_withdraw(p, prefix, pxlen, path_id, &last_id, &src);
  }
    }

 done:
  if (a)
    rta_free(a);

  if (err) /* Use subcode 9, not err */
    bgp_error(conn, 3, 9, NULL, 0);

  return;
}

#endif

static void
bgp_rx_update(struct bgp_conn *conn, byte *pkt, int len)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  byte *withdrawn, *attrs, *nlri;
  int withdrawn_len, attr_len, nlri_len;

  BGP_TRACE_RL(&rl_rcv_update, D_PACKETS, "Got UPDATE");

  /* Workaround for some BGP implementations that skip initial KEEPALIVE */
  if (conn->state == BS_OPENCONFIRM)
    bgp_conn_enter_established_state(conn);

  if (conn->state != BS_ESTABLISHED)
    { bgp_error(conn, 5, fsm_err_subcode[conn->state], NULL, 0); return; }
  bgp_start_timer(conn->hold_timer, conn->hold_time);

  /* Find parts of the packet and check sizes */
  if (len < 23)
    {
      bgp_error(conn, 1, 2, pkt+16, 2);
      return;
    }
  withdrawn = pkt + 21;
  withdrawn_len = get_u16(pkt + 19);
  if (withdrawn_len + 23 > len)
    goto malformed;
  attrs = withdrawn + withdrawn_len + 2;
  attr_len = get_u16(attrs - 2);
  if (withdrawn_len + attr_len + 23 > len)
    goto malformed;
  nlri = attrs + attr_len;
  nlri_len = len - withdrawn_len - attr_len - 23;
  if (!attr_len && nlri_len)
    goto malformed;
  DBG("Sizes: withdrawn=%d, attrs=%d, NLRI=%d\n", withdrawn_len, attr_len, nlri_len);

  lp_flush(bgp_linpool);

  bgp_do_rx_update(conn, withdrawn, withdrawn_len, nlri, nlri_len, attrs, attr_len);
  return;

malformed:
  bgp_error(conn, 3, 1, NULL, 0);
}

static struct {
  byte major, minor;
  byte *msg;
} bgp_msg_table[] = {
  { 1, 0, "Invalid message header" },
  { 1, 1, "Connection not synchronized" },
  { 1, 2, "Bad message length" },
  { 1, 3, "Bad message type" },
  { 2, 0, "Invalid OPEN message" },
  { 2, 1, "Unsupported version number" },
  { 2, 2, "Bad peer AS" },
  { 2, 3, "Bad BGP identifier" },
  { 2, 4, "Unsupported optional parameter" },
  { 2, 5, "Authentication failure" },
  { 2, 6, "Unacceptable hold time" },
  { 2, 7, "Required capability missing" }, /* [RFC5492] */
  { 2, 8, "No supported AFI/SAFI" }, /* This error msg is nonstandard */
  { 3, 0, "Invalid UPDATE message" },
  { 3, 1, "Malformed attribute list" },
  { 3, 2, "Unrecognized well-known attribute" },
  { 3, 3, "Missing mandatory attribute" },
  { 3, 4, "Invalid attribute flags" },
  { 3, 5, "Invalid attribute length" },
  { 3, 6, "Invalid ORIGIN attribute" },
  { 3, 7, "AS routing loop" },    /* Deprecated */
  { 3, 8, "Invalid NEXT_HOP attribute" },
  { 3, 9, "Optional attribute error" },
  { 3, 10, "Invalid network field" },
  { 3, 11, "Malformed AS_PATH" },
  { 4, 0, "Hold timer expired" },
  { 5, 0, "Finite state machine error" }, /* Subcodes are according to [RFC6608] */
  { 5, 1, "Unexpected message in OpenSent state" },
  { 5, 2, "Unexpected message in OpenConfirm state" },
  { 5, 3, "Unexpected message in Established state" },
  { 6, 0, "Cease" }, /* Subcodes are according to [RFC4486] */
  { 6, 1, "Maximum number of prefixes reached" },
  { 6, 2, "Administrative shutdown" },
  { 6, 3, "Peer de-configured" },
  { 6, 4, "Administrative reset" },
  { 6, 5, "Connection rejected" },
  { 6, 6, "Other configuration change" },
  { 6, 7, "Connection collision resolution" },
  { 6, 8, "Out of Resources" },
  { 7, 0, "Invalid ROUTE-REFRESH message" }, /* [RFC7313] */
  { 7, 1, "Invalid ROUTE-REFRESH message length" } /* [RFC7313] */
};

/**
 * bgp_error_dsc - return BGP error description
 * @code: BGP error code
 * @subcode: BGP error subcode
 *
 * bgp_error_dsc() returns error description for BGP errors
 * which might be static string or given temporary buffer.
 */
const char *
bgp_error_dsc(unsigned code, unsigned subcode)
{
  //log("--packet--%s",__func__);
  static char buff[32];
  unsigned i;
  for (i=0; i < ARRAY_SIZE(bgp_msg_table); i++)
    if (bgp_msg_table[i].major == code && bgp_msg_table[i].minor == subcode)
      {
  return bgp_msg_table[i].msg;
      }

  bsprintf(buff, "Unknown error %d.%d", code, subcode);
  return buff;
}

void
bgp_log_error(struct bgp_proto *p, u8 class, char *msg, unsigned code, unsigned subcode, byte *data, unsigned len)
{
  //log("--packet--%s",__func__);
  const byte *name;
  byte *t, argbuf[36];
  unsigned i;

  /* Don't report Cease messages generated by myself */
  if (code == 6 && class == BE_BGP_TX)
    return;

  name = bgp_error_dsc(code, subcode);
  t = argbuf;
  if (len)
    {
      *t++ = ':';
      *t++ = ' ';

      if ((code == 2) && (subcode == 2) && ((len == 2) || (len == 4)))
  {
    /* Bad peer AS - we would like to print the AS */
    t += bsprintf(t, "%d", (len == 2) ? get_u16(data) : get_u32(data));
    goto done;
  }
      if (len > 16)
  len = 16;
      for (i=0; i<len; i++)
  t += bsprintf(t, "%02x", data[i]);
    }
 done:
  *t = 0;
  log(L_REMOTE "%s: %s: %s%s", p->p.name, msg, name, argbuf);
}

static void
bgp_rx_notification(struct bgp_conn *conn, byte *pkt, int len)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;
  if (len < 21)
    {
      bgp_error(conn, 1, 2, pkt+16, 2);
      return;
    }

  unsigned code = pkt[19];
  unsigned subcode = pkt[20];
  int err = (code != 6);

  bgp_log_error(p, BE_BGP_RX, "Received", code, subcode, pkt+21, len-21);
  bgp_store_error(p, conn, BE_BGP_RX, (code << 16) | subcode);

#ifndef IPV6
  if ((code == 2) && ((subcode == 4) || (subcode == 7))
      /* Error related to capability:
       * 4 - Peer does not support capabilities at all.
       * 7 - Peer request some capability. Strange unless it is IPv6 only peer.
       */
      && (p->cf->capabilities == 2)
      /* Capabilities are not explicitly enabled or disabled, therefore heuristic is used */
      && (conn->start_state == BSS_CONNECT)
      /* Failed connection attempt have used capabilities */
      && (p->cf->remote_as <= 0xFFFF))
      /* Not possible with disabled capabilities */
    {
      /* We try connect without capabilities */
    //  log(L_WARN "%s: Capability related error received, retry with capabilities disabled", p->p.name);
      p->start_state = BSS_CONNECT_NOCAP;
      err = 0;
    }
#endif

  bgp_conn_enter_close_state(conn);
  bgp_schedule_packet(conn, PKT_SCHEDULE_CLOSE);

  if (err) 
    {
      bgp_update_startup_delay(p);
      bgp_stop(p, 0);
    }
}

static void
bgp_rx_keepalive(struct bgp_conn *conn)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;

  BGP_TRACE(D_PACKETS, "Got KEEPALIVE");
  bgp_start_timer(conn->hold_timer, conn->hold_time);
  switch (conn->state)
    {
    case BS_OPENCONFIRM:
      bgp_conn_enter_established_state(conn);
      break;
    case BS_ESTABLISHED:
      break;
    default:
      bgp_error(conn, 5, fsm_err_subcode[conn->state], NULL, 0);
    }
}

static void
bgp_rx_route_refresh(struct bgp_conn *conn, byte *pkt, int len)
{
  //log("--packet--%s",__func__);
  struct bgp_proto *p = conn->bgp;

  if (conn->state != BS_ESTABLISHED)
    { bgp_error(conn, 5, fsm_err_subcode[conn->state], NULL, 0); return; }

  if (!p->cf->enable_refresh)
    { bgp_error(conn, 1, 3, pkt+18, 1); return; }

  if (len < (BGP_HEADER_LENGTH + 4))
    { bgp_error(conn, 1, 2, pkt+16, 2); return; }

  if (len > (BGP_HEADER_LENGTH + 4))
    { bgp_error(conn, 7, 1, pkt, MIN(len, 2048)); return; }

  /* FIXME - we ignore AFI/SAFI values, as we support
     just one value and even an error code for an invalid
     request is not defined */

  /* RFC 7313 redefined reserved field as RR message subtype */
  uint subtype = conn->peer_enhanced_refresh_support ? pkt[21] : BGP_RR_REQUEST;

  switch (subtype)
  {
  case BGP_RR_REQUEST:
    BGP_TRACE(D_PACKETS, "Got ROUTE-REFRESH");
    proto_request_feeding(&p->p);
    break;

  case BGP_RR_BEGIN:
    BGP_TRACE(D_PACKETS, "Got BEGIN-OF-RR");
    bgp_refresh_begin(p);
    break;

  case BGP_RR_END:
    BGP_TRACE(D_PACKETS, "Got END-OF-RR");
    bgp_refresh_end(p);
    break;

  default:
    log(L_WARN "%s: Got ROUTE-REFRESH message with unknown subtype %u, ignoring",
  p->p.name, subtype);
    break;
  }
}


/**
 * bgp_rx_packet - handle a received packet
 * @conn: BGP connection
 * @pkt: start of the packet
 * @len: packet size
 *
 * bgp_rx_packet() takes a newly received packet and calls the corresponding
 * packet handler according to the packet type.
 */
static void
bgp_rx_packet(struct bgp_conn *conn, byte *pkt, unsigned len)
{
  //log("--packet--%s",__func__);
  byte type = pkt[18];

  //for (int i = 0; i < len; ++i)
  //  log("pkt[%d]: %d", i, pkt[i]);
  
  DBG("BGP: Got packet %02x (%d bytes)\n", type, len);

  if (conn->bgp->p.mrtdump & MD_MESSAGES)
    mrt_dump_bgp_packet(conn, pkt, len);

  switch (type)
    {
    case PKT_OPEN:    return bgp_rx_open(conn, pkt, len);
    case PKT_UPDATE:    return bgp_rx_update(conn, pkt, len);
    case PKT_NOTIFICATION:      return bgp_rx_notification(conn, pkt, len);
    case PKT_KEEPALIVE:   return bgp_rx_keepalive(conn);
    case PKT_ROUTE_REFRESH: return bgp_rx_route_refresh(conn, pkt, len);
    default:      bgp_error(conn, 1, 3, pkt+18, 1);
    }
}

/**
 * bgp_rx - handle received data
 * @sk: socket
 * @size: amount of data received
 *
 * bgp_rx() is called by the socket layer whenever new data arrive from
 * the underlying TCP connection. It assembles the data fragments to packets,
 * checks their headers and framing and passes complete packets to
 * bgp_rx_packet().
 */
int
bgp_rx(sock *sk, int size)
{
  //log("--packet--%s",__func__);
  struct bgp_conn *conn = sk->data;
  struct bgp_proto *p = conn->bgp;
  byte *pkt_start = sk->rbuf;
  byte *end = pkt_start + size;
  unsigned i, len;

  DBG("BGP: RX hook: Got %d bytes\n", size);
  while (end >= pkt_start + BGP_HEADER_LENGTH)
    {
      if ((conn->state == BS_CLOSE) || (conn->sk != sk))
  return 0;
      for(i=0; i<16; i++)
  if (pkt_start[i] != 0xff)
    {
      bgp_error(conn, 1, 1, NULL, 0);
      break;
    }
      len = get_u16(pkt_start+16);
      if (len < BGP_HEADER_LENGTH || len > bgp_max_packet_length(p))
  {
    bgp_error(conn, 1, 2, pkt_start+16, 2);
    break;
  }
      if (end < pkt_start + len)
  break;
      bgp_rx_packet(conn, pkt_start, len);
      pkt_start += len;
    }
  if (pkt_start != sk->rbuf)
    {
      memmove(sk->rbuf, pkt_start, end - pkt_start);
      sk->rpos = sk->rbuf + (end - pkt_start);
    }
  return 0;
}
