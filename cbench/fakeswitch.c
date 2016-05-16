#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <inttypes.h>

#include <openflow/openflow.h>

#include <sys/socket.h>
#include <sys/types.h>
#include <sys/time.h>

#include <net/ethernet.h>

#include <netinet/in.h>

#include "config.h"
#include "cbench.h"
#include "fakeswitch.h"

#ifdef USE_EPOLL
#include <sys/epoll.h>
#endif

static int debug_msg(struct fakeswitch * fs, char * msg, ...);

static int make_features_reply(struct fakeswitch *fs, int switch_id, int xid,
        char * buf, int buflen);
static int make_stats_desc_reply(struct ofp_multipart_request * req, char * buf,
        int buflen);
static int make_port_desc_reply(struct ofp_multipart_request * req, char * buf,
        int buflen);
static int make_table_features_reply(struct ofp_multipart_request * req,
        char * buf, int buflen);
static int parse_set_config(struct ofp_header * msg);
static int make_config_reply(int xid, char * buf, int buflen);
static int make_vendor_reply(int xid, char * buf, int buflen);
static int make_packet_in(int switch_id, int xid, int buffer_id, char * buf,
        int buflen, int mac_address);
static int packet_out_is_lldp(struct ofp_packet_out * po);
static void fakeswitch_handle_write(struct fakeswitch *fs);
static void fakeswitch_learn_dstmac(struct fakeswitch *fs);
void fakeswitch_change_status_now(struct fakeswitch *fs, int new_status);
void fakeswitch_change_status(struct fakeswitch *fs, int new_status);

static struct ofp_switch_config Switch_config = { .header = { OFP_VERSION,
        OFPT_GET_CONFIG_REPLY, sizeof(struct ofp_switch_config), 0 },
        .flags = 0, .miss_send_len = 0, };

static inline uint64_t htonll(uint64_t n) {
    return htonl(1) == 1 ? n : ((uint64_t) htonl(n) << 32) | htonl(n >> 32);
}

static inline uint64_t ntohll(uint64_t n) {
    return htonl(1) == 1 ? n : ((uint64_t) ntohl(n) << 32) | ntohl(n >> 32);
}

void fakeswitch_init(struct fakeswitch *fs, int dpid, int sock, int bufsize,
        int debug, int delay, enum test_mode mode, int total_mac_addresses,
        int learn_dstmac) {
    char buf[BUFLEN];
    fs->sock = sock;
    fs->debug = debug;
#ifdef USE_EPOLL
    fs->id = dpid;
#else
    static int ID = 1;
    fs->id = ID++;
#endif
    fs->inbuf = msgbuf_new(bufsize);
    fs->outbuf = msgbuf_new(bufsize);
    fs->probe_state = 0;
    fs->mode = mode;
    fs->probe_size = make_packet_in(fs->id, 0, 0, buf, BUFLEN,
            fs->current_mac_address++);
    fs->count = 0;
    fs->switch_status = START;
    fs->delay = delay;
    fs->total_mac_addresses = total_mac_addresses;
    fs->current_mac_address = 0;
    fs->xid = 1;
    fs->learn_dstmac = learn_dstmac;
    fs->current_buffer_id = 1;

    // we only send one bitmap containing version 1.4

    size_t version_bitmap_size = sizeof(struct ofp_hello_elem_versionbitmap)
            + sizeof(uint32_t);
    assert(version_bitmap_size == 8);

    struct ofp_hello_elem_versionbitmap *version_bitmap =
            (struct ofp_hello_elem_versionbitmap*) malloc(version_bitmap_size);

    version_bitmap->type = htons(OFPHET_VERSIONBITMAP);
    version_bitmap->length = htons(version_bitmap_size);

    // this bitmap (0x0000003e) represents 0x05 (OF 1.4)
    uint32_t bitmap_val = htonl(0x0000003e);
    memcpy(version_bitmap->bitmaps, &bitmap_val, sizeof(bitmap_val));

    size_t hello_size = sizeof(struct ofp_hello) + version_bitmap_size;
    assert(hello_size == 16);

    struct ofp_hello *ofph = (struct ofp_hello*) malloc(hello_size);
    ofph->header.version = OFP_VERSION;
    ofph->header.type = OFPT_HELLO;
    ofph->header.length = htons(hello_size);
    ofph->header.xid = htonl(1);
    memcpy(ofph->elements, version_bitmap, version_bitmap_size);

    // Send HELLO
    msgbuf_push(fs->outbuf, (char *) ofph, hello_size);
    debug_msg(fs, " sent hello");
}

void print_header(struct ofp_header header);
void print_packet_in(struct ofp_packet_in pi);
void print_match(struct ofp_match m);
void print_packet_in_data(char *buf, int startIndex, int dataLength);

void fakeswitch_learn_dstmac(struct fakeswitch *fs) {
    // thanks wireshark
    char gratuitous_arp_reply[] = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00,
            0x0c, 0x29, 0x1a, 0x29, 0x1a, 0x08, 0x06, 0x00, 0x01, 0x08, 0x00,
            0x06, 0x04, 0x00, 0x02, 0x00, 0x0c, 0x29, 0x1a, 0x29, 0x1a, 0x7f,
            0x00, 0x00, 0x01, 0x00, 0x0c, 0x29, 0x1a, 0x29, 0x1a, 0x7f, 0x00,
            0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, };

    char mac_address_to_learn[] = { 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01 };
    char ip_address_to_learn[] = { 192, 168, 1, 40 };

    char buf[512];

    uint8_t pad[2];
    memset(pad, 0, sizeof(pad));

    struct ofp_packet_in *pkt_in;

    /*
     printf("sizeof(inport): %lu\n", sizeof(in_port));
     printf("sizeof(OXM_OF_IN_PORT): %lu\n", sizeof(OXM_OF_IN_PORT));
     */

    struct ether_header * eth;
    void * arp_reply;

    memset(buf, 0, sizeof(buf));

    /*
     debug_msg(fs,
     "sizeof(ofp_packet_in)=%lu ; sizeof(ofp_header)=%lu ; sizeof(ofp_match)=%lu ; ",
     sizeof(struct ofp_packet_in), sizeof(struct ofp_header),
     sizeof(struct ofp_match));
     */

    /** create OF >= 1.2 match **/

    // OFPXMT_OPENFLOW_BASIC + OFPXMT_OFB_IN_PORT + has_mask + length (oxm field)
    uint32_t oxm_in_port = htonl(OXM_OF_IN_PORT);

    // in port (value of the field above)
    uint32_t in_port = htonl(2);

    /*
     printf("Creating match...\n");
     printf("oxm_in_port = \t%08x (size: %lu)\n", oxm_in_port,
     sizeof(OXM_OF_IN_PORT));
     printf("in_port = \t%08x (size: %lu)\n", in_port, sizeof(in_port));
     */

    // OXM_OF_IN_PORT (4) + size of in_port (4)
    size_t fields_len = sizeof(oxm_in_port) + sizeof(in_port);

    //printf("Length of fields: %lu\n", fields_len);

    // sizeof(struct ofp_match) = 8 (2*uint16_t + pad[4]) + fields_len (8) = 16
    size_t match_size = sizeof(struct ofp_match) + fields_len;

    struct ofp_match *pkt_in_match = (struct ofp_match*) malloc(match_size);

    /*printf("Allocated %lu for pkt_in_match (%lu for struct ofp_match + "
     "%lu for pkt_in_match->oxm_fields)\n", match_size,
     sizeof(struct ofp_match), fields_len);*/

    pkt_in_match->type = htons(OFPMT_OXM);
    // size of OXM_OF_IN_PORT + size of in_port
    pkt_in_match->length = htons(fields_len + sizeof(pkt_in_match->pad));

    //assert(sizeof(oxm_in_port) == sizeof(OXM_OF_IN_PORT));

    uint32_t oxm_fields[fields_len];
    oxm_fields[0] = oxm_in_port;
    oxm_fields[1] = in_port;

    /*
     printf("oxm_fields[0] =\t%08x \n", oxm_fields[0]);
     printf("oxm_fields[1] =\t%08x \n", oxm_fields[1]);
     */

    memcpy(pkt_in_match->oxm_fields, oxm_fields, fields_len);

    /*
     memcpy(pkt_in_match->oxm_fields, (&oxm_in_port), sizeof(oxm_in_port));

     printf("Copied %lu bytes to pkt_in_match->oxm_fields from "
     "oxm_in_port (%08x)\n", sizeof(oxm_in_port), oxm_in_port);
     printf("pkt_in_match->oxm_fields =\t%08x \n", *pkt_in_match->oxm_fields);

     memcpy(pkt_in_match->oxm_fields + sizeof(oxm_in_port), &in_port,
     sizeof(in_port));

     printf("Copied %lu bytes to pkt_in_match->oxm_fields+%lu from "
     "in_port (%08x)\n", sizeof(in_port), sizeof(oxm_in_port), in_port);

     printf("pkt_in_match->oxm_fields =\t%08x \n", *pkt_in_match->oxm_fields);

     printf("pkt_in_match->oxm_fields + %lu =\t%08x \n", sizeof(oxm_in_port),
     (*(pkt_in_match->oxm_fields + sizeof(oxm_in_port))));

     //memcpy(pkt_in_match->oxm_fields, oxm_fields, sizeof(oxm_fields));
     */

    // match pad
    uint8_t match_pad[4];
    memset(match_pad, 0, sizeof(match_pad));
    memcpy(pkt_in_match->oxm_fields + fields_len, match_pad, sizeof(match_pad));

    /*
     debug_msg(fs, "Match after creation:");
     print_match(*pkt_in_match);
     */

    // build packet_in
    pkt_in = (struct ofp_packet_in *) buf;

    pkt_in->header.version = OFP_VERSION;
    pkt_in->header.type = OFPT_PACKET_IN;

    // add variable match size
    int len = sizeof(struct ofp_packet_in) + fields_len
            + sizeof(gratuitous_arp_reply) + sizeof(pad);

    pkt_in->header.length = htons(len);
    pkt_in->header.xid = htonl(fs->xid++);

    pkt_in->buffer_id = -1;
    pkt_in->total_len = htons(sizeof(gratuitous_arp_reply));

    pkt_in->reason = OFPR_TABLE_MISS;

    pkt_in->table_id = 0;

    pkt_in->cookie = 0;

    /*
     debug_msg(fs, "Match before memcpy:");
     print_match(*pkt_in_match);
     */

    // copy match to packet in
    memcpy(&(pkt_in->match), pkt_in_match,
            sizeof(struct ofp_match) + fields_len);
    /*
     debug_msg(fs, "PacketIn->Match after memcpy:");
     print_match(pkt_in->match);
     debug_msg(fs, "Match after memcpy:");
     print_match(*pkt_in_match);
     */

    // need to add pad[2] here after match
    // we start right after the match
    int index = sizeof(struct ofp_packet_in) + fields_len;

    memcpy(&buf[index], pad, sizeof(pad));

    index = index + sizeof(pad);

    /*
     debug_msg(fs,
     "Starting to copy %lu bytes to buffer init position %d. PacketIn len = %d",
     sizeof(gratuitous_arp_reply), index, len);
     */

    memcpy(&buf[index], gratuitous_arp_reply, sizeof(gratuitous_arp_reply));

    /*
     debug_msg(fs, "PacketIn after memcpy:");
     print_packet_in(*pkt_in);
     print_packet_in_data(buf, index, sizeof(gratuitous_arp_reply));
     */

    mac_address_to_learn[5] = fs->id;
    ip_address_to_learn[2] = fs->id;

    eth = (struct ether_header *) &(buf[index]);
    memcpy(eth->ether_shost, mac_address_to_learn, 6);

    arp_reply = ((void *) eth) + sizeof(struct ether_header);
    memcpy(arp_reply + 8, mac_address_to_learn, 6);
    memcpy(arp_reply + 14, ip_address_to_learn, 4);
    memcpy(arp_reply + 18, mac_address_to_learn, 6);
    memcpy(arp_reply + 24, ip_address_to_learn, 4);

    /*
     debug_msg(fs, "PacketIn after arp_reply:");
     print_packet_in(*pkt_in);
     */

    /*
     printf("Whole buffern:\n");
     int i;
     for (i = 0; i < len; i++) {
     printf("%02x ", buf[i]);
     }
     printf("\n");
     */
    msgbuf_push(fs->outbuf, (char *) pkt_in, len);
    debug_msg(fs,
            " sent gratuitous ARP reply to learn about mac address: version %d length %d type %d eth: %x arp: %x ",
            pkt_in->header.version, len, buf[1], eth, arp_reply);
}

void print_packet_in_data(char *buf, int startIndex, int dataLength) {
    printf("PacketIn data:\n");
    int i;
    for (i = startIndex; i < startIndex + dataLength; i++) {
        printf("%02x ", buf[i]);
    }
    printf("\n");
}

void print_header(struct ofp_header header) {
    printf("Header: version=%d , type=%d , xid=%u , length=%d \n",
            header.version, header.type, ntohl(header.xid),
            ntohs(header.length));
}

void print_packet_in(struct ofp_packet_in pi) {
    print_header(pi.header);
    printf("reason=%d , cookie=%lu , table_id=%d , buffer_id=%d,"
            "total_len=%d \n", pi.reason, pi.cookie, pi.table_id, pi.buffer_id,
            ntohs(pi.total_len));
    print_match(pi.match);
}

void print_match(struct ofp_match m) {
    printf("match=[type=%d , length=%d , fields=", ntohs(m.type),
            ntohs(m.length));
    int i;
    for (i = 0; i < ntohs(m.length); i += 4) {
        printf("%08x ", m.oxm_fields[i]);
    }
    printf("]\n");
}

/***********************************************************************/

void fakeswitch_set_pollfd(struct fakeswitch *fs, struct pollfd *pfd) {
    pfd->events = POLLIN | POLLOUT;
    pfd->fd = fs->sock;
}

/***********************************************************************/

int fakeswitch_get_count(struct fakeswitch *fs) {
    int ret = fs->count;
    int count;
    int msglen;
    struct ofp_header * ofph;
    fs->count = 0;
    fs->probe_state = 0;        // reset packet state
    // keep reading until there is nothing to clear out the queue
    while ((count = msgbuf_read(fs->inbuf, fs->sock)) > 0) {
        while (count > 0) {
            // need to read msg by msg to ensure framing isn't broken
            ofph = msgbuf_peek(fs->inbuf);
            msglen = ntohs(ofph->length);
            if (count < msglen)
                break;     // msg not all there yet; 
            msgbuf_pull(fs->inbuf, NULL, ntohs(ofph->length));
            count -= msglen;
        }
    }
    return ret;
}

/***********************************************************************/
static int parse_set_config(struct ofp_header * msg) {
    struct ofp_switch_config * sc;
    assert(msg->type == OFPT_SET_CONFIG);
    sc = (struct ofp_switch_config *) msg;
    memcpy(&Switch_config, sc, sizeof(struct ofp_switch_config));

    return 0;
}

/***********************************************************************/
static int make_config_reply(int xid, char * buf, int buflen) {
    int len = sizeof(struct ofp_switch_config);
    assert(buflen >= len);
    Switch_config.header.type = OFPT_GET_CONFIG_REPLY;
    Switch_config.header.xid = xid;
    memcpy(buf, &Switch_config, len);

    return len;
}

/***********************************************************************/

// TODO: remove fakeswitch argument
static int make_features_reply(struct fakeswitch *fs, int id, int xid,
        char * buf, int buflen) {
    struct ofp_switch_features * features;
    /*
     const char fake[] =     // stolen from wireshark
     {
     0x97, 0x06, 0x00, 0xe0, 0x04, 0x01, 0x00, 0x00, 0x00, 0x00, 0x76,
     0xa9, 0xd4, 0x0d, 0x25, 0x48, 0x00, 0x00, 0x01, 0x00, 0x02,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07,
     0xff, 0x00, 0x01, 0x1a, 0xc1, 0x51, 0xff, 0xef, 0x8a, 0x76,
     0x65, 0x74, 0x68, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x02, 0xce, 0x2f, 0xa2, 0x87, 0xf6, 0x70, 0x76, 0x65, 0x74,
     0x68, 0x33, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xca,
     0x8a, 0x1e, 0xf3, 0x77, 0xef, 0x76, 0x65, 0x74, 0x68, 0x35,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0xfa, 0xbc, 0x77,
     0x8d, 0x7e, 0x0b, 0x76, 0x65, 0x74, 0x68, 0x37, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00 };
     */

    // taken from ovs/tests/ofp-print.at OFPT_FEATURES_REPLY - OF1.3
    // (changed 0x04 to 0x05 - OFVersion)
    const char fake[] = { 0x05, 0x06, 0x00, 0x20, 0x00, 0x00, 0x00, 0x01, 0x00,
            0x00, 0x50, 0x54, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x01, 0x00,
            0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x77, 0x00, 0x00, 0x00,
            0x00 };

    assert(buflen > sizeof(fake));
    memcpy(buf, fake, sizeof(fake));
    features = (struct ofp_switch_features *) buf;
    features->header.version = OFP_VERSION;
    features->header.xid = xid;
    features->datapath_id = htonll(id);

    debug_msg(fs, "features reply: version=%d; type=%d; length=%u; xid=%lu",
            features->header.version, features->header.type,
            features->header.length, features->header.xid);

    return sizeof(fake);
}

/***********************************************************************/

static int make_stats_desc_reply(struct ofp_multipart_request * req, char * buf,
        int buflen) {

    printf("make_stats_desc_reply\n");

    struct ofp_desc cbench_desc = { .mfr_desc =
            "Cbench - controller I/O benchmark", .hw_desc =
            "this is actually software...", .sw_desc = "version " VERSION,
            .serial_num = "none", .dp_desc = "none" };
    struct ofp_multipart_reply * reply;

    int reply_len = sizeof(struct ofp_multipart_reply)
            + sizeof(struct ofp_desc);

    assert(BUFLEN > reply_len);

    // use request as initial template
    memcpy(buf, req, sizeof(*req));
    reply = (struct ofp_multipart_reply *) buf;
    // we only need to change the type and length of the header.
    reply->header.type = OFPT_MULTIPART_REPLY;
    reply->header.length = htons(reply_len);

    reply->type = OFPMP_DESC;
    reply->flags = 0;
    memcpy(reply->body, &cbench_desc, sizeof(cbench_desc));

    return reply_len;
}

static int make_port_desc_reply(struct ofp_multipart_request * req, char * buf,
        int buflen) {

    // taken from wireshark - communication between ovs and floodlight
    const char fake[] = { 0x05, 0x13, 0x00, 0xe8, 0x00, 0x00, 0x00, 0x11, 0x00,
            0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xfe,
            0x00, 0x48, 0x00, 0x00, 0xb6, 0x9e, 0xae, 0x15, 0xa7, 0x4c, 0x00,
            0x00, 0x73, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,
            0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x48, 0x00, 0x00, 0xee,
            0x1d, 0xbe, 0xf2, 0x43, 0x3b, 0x00, 0x00, 0x73, 0x31, 0x2d, 0x65,
            0x74, 0x68, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x40, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x98, 0x96, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x02, 0x00, 0x48, 0x00, 0x00, 0x9a, 0x67, 0x4f, 0x9d, 0x95, 0x3b,
            0x00, 0x00, 0x73, 0x31, 0x2d, 0x65, 0x74, 0x68, 0x32, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x08, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x98, 0x96, 0x80, 0x00,
            0x00, 0x00, 0x00 };

    struct ofp_multipart_reply *reply;
    assert(buflen > sizeof(fake));
    memcpy(buf, fake, sizeof(fake));
    reply = (struct ofp_multipart_reply *) buf;
    reply->header.version = OFP_VERSION;
    reply->header.xid = req->header.xid;

    return sizeof(fake);
}

static int make_table_features_reply(struct ofp_multipart_request * req,
        char * buf, int buflen) {

    printf("make_table_features_reply\n");

    // 1. build properties that will go to the properties of table_features

    // Taken from first table feature property inside the first table features
    // sent by an ovs.

    // Type: OFPTFPT_INSTRUCTIONS (0)
    // Length: 28
    // Followed by 6 Instruction ID
    // Ends with pad 00000000
    const char fake_properties[] = { 0x00, 0x00, 0x00, 0x1c, 0x00, 0x01, 0x00,
            0x04, 0x00, 0x02, 0x00, 0x04, 0x00, 0x03, 0x00, 0x04, 0x00, 0x04,
            0x00, 0x04, 0x00, 0x05, 0x00, 0x04, 0x00, 0x06, 0x00, 0x04 };
    size_t fake_properties_size = sizeof(fake_properties);

    // 2. build table_features that will go to the body of the multipart_reply
    size_t table_features_size = sizeof(struct ofp_table_features)
            + fake_properties_size;

    struct ofp_table_features *features = (struct ofp_table_features*) malloc(
            table_features_size);
    printf("table_features_size=%d\n", table_features_size);

    features->length = htons(table_features_size);
    features->table_id = 0;
    strcpy(features->name, "classifier");
    features->metadata_match = 18446744073709551615;
    features->metadata_write = 18446744073709551615;
    features->capabilities = 0x00000000;
    features->max_entries = 1000000;

    memcpy(features->properties, fake_properties, fake_properties_size);

    // 3. build multipart_reply

    struct ofp_multipart_reply * reply;

    // len = struct members + body
    size_t reply_len = sizeof(struct ofp_multipart_reply) + table_features_size;

    printf("fake_properties_size=%lu\n"
            "sizeof(struct ofp_table_features)=%lu\n"
            "table_features_size=%lu\n"
            "sizeof(struct ofp_multipart_reply)=%lu\n"
            "reply_len=%lu\n", fake_properties_size,
            sizeof(struct ofp_table_features), table_features_size,
            sizeof(struct ofp_multipart_reply), reply_len);

    assert(BUFLEN > reply_len);

    // use request as initial template
    memcpy(buf, req, sizeof(*req));
    reply = (struct ofp_multipart_reply *) buf;
    // we only need to change the type and length of the header.
    reply->header.type = OFPT_MULTIPART_REPLY;
    reply->header.length = htons(reply_len);
    reply->type = OFPMP_TABLE_FEATURES;
    reply->flags = 0;
    memset(reply->pad, 0, 4);
    memcpy(reply->body, features, table_features_size);

    return reply_len;
}

/***********************************************************************/
static int make_vendor_reply(int xid, char * buf, int buflen) {
    struct ofp_error_msg * e;
    assert(buflen > sizeof(struct ofp_error_msg));
    e = (struct ofp_error_msg *) buf;
    e->header.type = OFPT_ERROR;
    e->header.version = OFP_VERSION;
    e->header.length = htons(sizeof(struct ofp_error_msg));
    e->header.xid = xid;
    e->type = htons(OFPET_BAD_REQUEST);
    e->code = htons(OFPBRC_BAD_EXPERIMENTER);
    return sizeof(struct ofp_error_msg);
}
/***********************************************************************
 *  return 1 if the embedded packet in the packet_out is lldp
 *
 */

#ifndef ETHERTYPE_LLDP
#define ETHERTYPE_LLDP 0x88cc
#endif

static int packet_out_is_lldp(struct ofp_packet_out * po) {
    char * ptr = (char *) po;
    ptr += sizeof(struct ofp_packet_out) + ntohs(po->actions_len);
    struct ether_header * ethernet = (struct ether_header *) ptr;
    unsigned short ethertype = ntohs(ethernet->ether_type);
    if (ethertype == ETHERTYPE_VLAN) {
        ethernet = (struct ether_header *) ((char *) ethernet) + 4;
        ethertype = ntohs(ethernet->ether_type);
    }

    return ethertype == ETHERTYPE_LLDP;
}

/***********************************************************************/
static int make_packet_in(int switch_id, int xid, int buffer_id, char * buf,
        int buflen, int mac_address) {
    struct ofp_packet_in * pi;
    struct ether_header * eth;
    /* OF_PACKET_IN (OF1.0)
     const char fake[] = { 0x97, 0x0a, 0x00, 0x52, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x01, 0x01, 0x00, 0x40, 0x00, 0x01, 0x00, 0x00, 0x80, 0x00,
     0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x08,
     0x00, 0x45, 0x00, 0x00, 0x32, 0x00, 0x00, 0x00, 0x00, 0x40, 0xff,
     0xf7, 0x2c, 0xc0, 0xa8, 0x00, 0x28, 0xc0, 0xa8, 0x01, 0x28, 0x7a,
     0x18, 0x58, 0x6b, 0x11, 0x08, 0x97, 0xf5, 0x19, 0xe2, 0x65, 0x7e,
     0x07, 0xcc, 0x31, 0xc3, 0x11, 0xc7, 0xc4, 0x0c, 0x8b, 0x95, 0x51,
     0x51, 0x33, 0x54, 0x51, 0xd5, 0x00, 0x36 };*/

    /*OFPT_PACKET_IN (OF1.4)
     * (xid=0x0): cookie=0x102030405060708 total_len=42
     * in_port=LOCAL (via no_match) data_len=42 buffer=0xffffff00
     * rarp,vlan_tci=0x0000,dl_src=00:23:20:83:c1:5f,dl_dst=ff:ff:ff:ff:ff:ff,
     * arp_spa=0.0.0.0,arp_tpa=0.0.0.0,arp_op=3,arp_sha=00:23:20:83:c1:5f,
     * arp_tha=00:23:20:83:c1:5f
     */
    const char fake[] = { 0x05, 0x0a, 0x00, 0x54, 0x00, 0x00, 0x00, 0x00, 0xff,
            0xff, 0xff, 0x00, 0x00, 0x2a, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04,
            0x05, 0x06, 0x07, 0x08, 0x00, 0x01, 0x00, 0x0c, 0x80, 0x00, 0x00,
            0x04, 0xff, 0xff, 0xff, 0xfe, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x23, 0x20, 0x83, 0xc1,
            0x5f, 0x80, 0x35, 0x00, 0x01, 0x08, 0x00, 0x06, 0x04, 0x00, 0x03,
            0x00, 0x23, 0x20, 0x83, 0xc1, 0x5f, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x23, 0x20, 0x83, 0xc1, 0x5f, 0x00, 0x00, 0x00, 0x00 };

    assert(buflen > sizeof(fake));
    memcpy(buf, fake, sizeof(fake));
    pi = (struct ofp_packet_in *) buf;
    pi->header.version = OFP_VERSION;
    pi->header.xid = htonl(xid);
    pi->buffer_id = htonl(buffer_id);
    eth = (struct ether_header *) &(pi->match) + 1; // TODO ??
// copy into src mac addr; only 4 bytes, but should suffice to not confuse
// the controller; don't overwrite first byte
    memcpy(&eth->ether_shost[1], &mac_address, sizeof(mac_address));
// mark this as coming from us, mostly for debug
    eth->ether_dhost[5] = switch_id;
    eth->ether_shost[5] = switch_id;
    return sizeof(fake);
}

void fakeswitch_change_status_now(struct fakeswitch *fs, int new_status) {
    fs->switch_status = new_status;
    if (new_status == READY_TO_SEND) {
        fs->count = 0;
        fs->probe_state = 0;
    }

}

void fakeswitch_change_status(struct fakeswitch *fs, int new_status) {
    if (fs->delay == 0) {
        fakeswitch_change_status_now(fs, new_status);
        debug_msg(fs, " switched to next status %d", new_status);
    } else {
        fs->switch_status = WAITING;
        fs->next_status = new_status;
        gettimeofday(&fs->delay_start, NULL);
        fs->delay_start.tv_sec += fs->delay / 1000;
        fs->delay_start.tv_usec += (fs->delay % 1000) * 1000;
        debug_msg(fs, " delaying next status %d by %d ms", new_status,
                fs->delay);
    }

}

/***********************************************************************/
void fakeswitch_handle_read(struct fakeswitch *fs) {
    int count;
    struct ofp_header * ofph;
    struct ofp_header echo;
    struct ofp_header barrier;
    char buf[BUFLEN];
    count = msgbuf_read(fs->inbuf, fs->sock);   // read any queued data
    if (count <= 0) {
        fprintf(stderr, "controller msgbuf_read() = %d:  ", count);
        if (count < 0)
            perror("msgbuf_read");
        else
            fprintf(stderr, " closed connection ");
        fprintf(stderr, "... exiting\n");
        exit(1);
    }
    while ((count = msgbuf_count_buffered(fs->inbuf))
            >= sizeof(struct ofp_header)) {
        ofph = msgbuf_peek(fs->inbuf);
        if (count < ntohs(ofph->length))
            return;     // msg not all there yet
        msgbuf_pull(fs->inbuf, NULL, ntohs(ofph->length));
        switch (ofph->type) {

        struct ofp_flow_mod * fm;
        struct ofp_packet_out *po;
        struct ofp_multipart_request * stats_req;
    case OFPT_PACKET_OUT:
        po = (struct ofp_packet_out *) ofph;
        if (fs->switch_status == READY_TO_SEND && !packet_out_is_lldp(po)) {
            // assume this is in response to what we sent
            fs->count++;        // got response to what we went
            fs->probe_state--;
            // TODO: send packet in to the controller here?
            debug_msg(fs, "Received PacketOut!!!");
        }
        break;
    case OFPT_FLOW_MOD:
        fm = (struct ofp_flow_mod *) ofph;
        if (fs->switch_status == READY_TO_SEND
                && (fm->command == htons(OFPFC_ADD)
                        || fm->command == htons(OFPFC_MODIFY_STRICT))) {
            fs->count++;        // got response to what we went
            fs->probe_state--;
        }
        break;
    case OFPT_FEATURES_REQUEST:
        // pull msgs out of buffer
        debug_msg(fs, "got feature_req");
        // Send features reply
        count = make_features_reply(fs, fs->id, ofph->xid, buf, BUFLEN);
        msgbuf_push(fs->outbuf, buf, count);
        debug_msg(fs, "sent feature_rsp");
        fakeswitch_change_status(fs,
                fs->learn_dstmac ? LEARN_DSTMAC : READY_TO_SEND);
        break;
    case OFPT_SET_CONFIG:
        // pull msgs out of buffer
        debug_msg(fs, "parsing set_config");
        parse_set_config(ofph);
        break;
    case OFPT_GET_CONFIG_REQUEST:
        // pull msgs out of buffer
        debug_msg(fs, "got get_config_request");
        count = make_config_reply(ofph->xid, buf, BUFLEN);
        msgbuf_push(fs->outbuf, buf, count);
        if ((fs->mode == MODE_LATENCY) && (fs->probe_state == 1)) {
            fs->probe_state = 0;       // restart probe state b/c some
            // controllers block on config
            debug_msg(fs, "reset probe state b/c of get_config_reply");
        }
        debug_msg(fs, "sent get_config_reply");
        break;
    case OFPT_EXPERIMENTER:
        // pull msgs out of buffer
        debug_msg(fs, "got vendor");
        count = make_vendor_reply(ofph->xid, buf, BUFLEN);
        msgbuf_push(fs->outbuf, buf, count);
        debug_msg(fs, "sent vendor");
        // apply nox hack; nox ignores packet_in until this msg is sent
        fs->probe_state = 0;
        break;
    case OFPT_HELLO:
        debug_msg(fs, "got hello from controller");
        // we already sent our own HELLO; don't respond
        break;
    case OFPT_ECHO_REQUEST:
        debug_msg(fs, "got echo, sent echo_resp");
        echo.version = OFP_VERSION;
        echo.length = htons(sizeof(echo));
        echo.type = OFPT_ECHO_REPLY;
        echo.xid = ofph->xid;
        msgbuf_push(fs->outbuf, (char *) &echo, sizeof(echo));
        break;
    case OFPT_BARRIER_REQUEST:
        debug_msg(fs, "got barrier, sent barrier_resp");
        barrier.version = OFP_VERSION;
        barrier.length = htons(sizeof(barrier));
        barrier.type = OFPT_BARRIER_REPLY;
        barrier.xid = ofph->xid;
        msgbuf_push(fs->outbuf, (char *) &barrier, sizeof(barrier));
        break;
    case OFPT_MULTIPART_REQUEST:
        stats_req = (struct ofp_multipart_request *) ofph;
        uint16_t multipart_type = ntohs(stats_req->type);
        int valid = 1;

        debug_msg(fs, "Got multipart_req:");
        print_header(stats_req->header);
        printf("multipart_type: %u\n", multipart_type);

        switch (multipart_type) {
        case OFPMP_PORT_DESC:
            count = make_port_desc_reply(stats_req, buf, BUFLEN);
            debug_msg(fs, "Sending port description reply");
            break;
        case OFPMP_DESC:
            count = make_stats_desc_reply(stats_req, buf, BUFLEN);
            debug_msg(fs, "Sending description stats_reply");
            break;
        case OFPMP_TABLE_FEATURES:
            count = make_table_features_reply(stats_req, buf, BUFLEN);
            debug_msg(fs, "Sending table features reply");
            break;
        default:
            debug_msg(fs, "Silently ignoring multipart_request msg. "
                    "Type is %d\n", multipart_type);
            valid = 0;
        } // end switch (multipart_type) in main case OFPT_MULTIPART_REQUEST

        if (valid == 1) {
            msgbuf_push(fs->outbuf, buf, count);
            if ((fs->mode == MODE_LATENCY) && (fs->probe_state == 1)) {
                fs->probe_state = 0;     // restart probe state b/c some
                // controllers block on config
                debug_msg(fs, "reset probe state b/c of multipart_request");
            }
        }

        break;

    default:
        fprintf(stderr, "Ignoring OpenFlow message type %d\n", ofph->type);

        }; // end switch (ofph->type)

        if (fs->probe_state < 0) {
            debug_msg(fs, "WARN: Got more responses than probes!!: : %d",
                    fs->probe_state);
            fs->probe_state = 0;
        }
    }
}
/***********************************************************************/
static void fakeswitch_handle_write(struct fakeswitch *fs) {
    char buf[BUFLEN];
    int count;
    int send_count = 0;
    int throughput_buffer = BUFLEN;
    int i;
    if (fs->switch_status == READY_TO_SEND) {
        if ((fs->mode == MODE_LATENCY) && (fs->probe_state == 0))
            send_count = 1;                 // just send one packet
        else if ((fs->mode == MODE_THROUGHPUT)
                && (msgbuf_count_buffered(fs->outbuf) < throughput_buffer)) // keep buffer full
            send_count = (throughput_buffer - msgbuf_count_buffered(fs->outbuf))
                    / fs->probe_size;
        for (i = 0; i < send_count; i++) {
            // queue up packet

            fs->probe_state++;
            // TODO come back and remove this copy
            count = make_packet_in(fs->id, fs->xid++, fs->current_buffer_id,
                    buf,
                    BUFLEN, fs->current_mac_address);
            fs->current_mac_address = (fs->current_mac_address + 1)
                    % fs->total_mac_addresses;
            fs->current_buffer_id =
                    (fs->current_buffer_id + 1) % NUM_BUFFER_IDS;
            msgbuf_push(fs->outbuf, buf, count);
            debug_msg(fs, "send message %d", i);
        }
    } else if (fs->switch_status == WAITING) {
        struct timeval now;
        gettimeofday(&now, NULL);
        if (timercmp(&now, &fs->delay_start, >)) {
            fakeswitch_change_status_now(fs, fs->next_status);
            debug_msg(fs, " delay is over: switching to state %d",
                    fs->next_status);
        }
    } else if (fs->switch_status == LEARN_DSTMAC) {
        // we should learn the dst mac addresses
        fakeswitch_learn_dstmac(fs);
        fakeswitch_change_status(fs, READY_TO_SEND);
    }
// send any data if it's queued
    if ( msgbuf_count_buffered(fs->outbuf) > 0)
        msgbuf_write(fs->outbuf, fs->sock, 0);
}
/***********************************************************************/
void fakeswitch_handle_io(struct fakeswitch *fs, void *pfd_events) {
#ifdef USE_EPOLL
    int events = *((int*) pfd_events);
    if (events & EPOLLIN) {
        fakeswitch_handle_read(fs);
    } else if (events & EPOLLOUT) {
        fakeswitch_handle_write(fs);
    }
#else
    struct pollfd *pfd = (struct pollfd*)pfd_events;
    if(pfd->revents & POLLIN)
    fakeswitch_handle_read(fs);
    if(pfd->revents & POLLOUT)
    fakeswitch_handle_write(fs);
#endif
}
/************************************************************************/
static int debug_msg(struct fakeswitch * fs, char * msg, ...) {
    va_list aq;
    if (fs->debug == 0)
        return 0;
    fprintf(stderr, "\n-------Switch %d: ", fs->id);
    va_start(aq, msg);
    vfprintf(stderr, msg, aq);
    if (msg[strlen(msg) - 1] != '\n')
        fprintf(stderr, "\n");
    return 1;
}
