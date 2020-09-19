#include "idris_buffer.h"
#include <sys/stat.h>
#include <string.h>

void* idris2_newBuffer(int bytes) {
    size_t size = sizeof(Buffer) + bytes*sizeof(uint8_t);

    Buffer* buf = malloc(size);
    if (buf == NULL) {
        return NULL;
    }

    buf->size = bytes;
//    memset(buf->data, 0, bytes);

    return (void*)buf;
}

void idris2_freeBuffer(void* buf) {
    free(buf);
}

void idris2_copyBuffer(void* from, int start, int len,
                       void* to, int loc) {
    Buffer* bfrom = from;
    Buffer* bto = to;

    if (loc >= 0 && loc+len <= bto->size) {
        memcpy(bto->data + loc, bfrom->data + start, len);
    }
}

int idris2_getBufferSize(void* buffer) {
    return ((Buffer*)buffer)->size;
}

void idris2_setBufferByte(void* buffer, int loc, int byte) {
    Buffer* b = buffer;
    if (loc >= 0 && loc < b->size) {
        b->data[loc] = byte;
    }
}

void idris2_setBufferInt(void* buffer, int loc, int64_t val) {
    Buffer* b = buffer;
    if (loc >= 0 && loc+3 < b->size) {
        b->data[loc  ] =  val        & 0xff;
        b->data[loc+1] = (val >>  8) & 0xff;
        b->data[loc+2] = (val >> 16) & 0xff;
        b->data[loc+3] = (val >> 24) & 0xff;
        b->data[loc+4] = (val >> 32) & 0xff;
        b->data[loc+5] = (val >> 40) & 0xff;
        b->data[loc+6] = (val >> 48) & 0xff;
        b->data[loc+7] = (val >> 56) & 0xff;
    }
}

void idris2_setBufferDouble(void* buffer, int loc, double val) {
    Buffer* b = buffer;
    // I am not proud of this
    if (loc >= 0 && loc + sizeof(double) <= b->size) {
        unsigned char* c = (unsigned char*)(& val);
        int i;
        for (i = 0; i < sizeof(double); ++i) {
            b->data[loc+i] = c[i];
        }
    }
}

void idris2_setBufferString(void* buffer, int loc, char* str) {
    Buffer* b = buffer;
    int len = strlen(str);

    if (loc >= 0 && loc+len <= b->size) {
        memcpy((b->data)+loc, str, len);
    }
}

uint8_t idris2_getBufferByte(void* buffer, int loc) {
    Buffer* b = buffer;
    if (loc >= 0 && loc < b->size) {
        return b->data[loc];
    } else {
        return 0;
    }
}

int64_t idris2_getBufferInt(void* buffer, int loc) {
    Buffer* b = buffer;
    if (loc >= 0 && loc+7 < b->size) {
        int64_t result = 0;
        for (size_t i=0; i<8; i++) {
            result |= b->data[loc + i] << (8 * i);
        }
        return result;
    } else {
        return 0;
    }
}

double idris2_getBufferDouble(void* buffer, int loc) {
    Buffer* b = buffer;
    double d;
    // I am even less proud of this
    unsigned char *c = (unsigned char*)(& d);
    if (loc >= 0 && loc + sizeof(double) <= b->size) {
        int i;
        for (i = 0; i < sizeof(double); ++i) {
            c[i] = b->data[loc+i];
        }
        return d;
    }
    else {
        return 0;
    }
}

char* idris2_getBufferString(void* buffer, int loc, int len) {
    Buffer* b = buffer;
    char * s = (char*)(b->data + loc);
    char * rs = malloc(len + 1);
    strncpy(rs, s, len);
    rs[len] = '\0';
    return rs;
}

size_t idris2_readBufferData(FILE* h, char* buffer, size_t loc, size_t max) {
    return fread(buffer+loc, sizeof(uint8_t), (size_t)max, h);
}

size_t idris2_writeBufferData(FILE* h, const char* buffer, size_t loc, size_t len) {
    return fwrite(buffer+loc, sizeof(uint8_t), len, h);
}
