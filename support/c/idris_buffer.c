#include "idris_buffer.h"
#include <sys/stat.h>
#include <string.h>

typedef struct {
    int size;
    uint8_t data[0];
} Buffer;

void* idris2_newBuffer(int bytes) {
    size_t size = sizeof(Buffer) + bytes*sizeof(uint8_t);

    Buffer* buf = malloc(size);
    if (buf == NULL) {
        return NULL;
    }

    buf->size = bytes;
    memset(buf->data, 0, bytes);

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

void idris2_setBufferInt(void* buffer, int loc, int val) {
    Buffer* b = buffer;
    if (loc >= 0 && loc+3 < b->size) {
        b->data[loc] = val & 0xff;
        b->data[loc+1] = (val >> 8) & 0xff;
        b->data[loc+2] = (val >> 16) & 0xff;
        b->data[loc+3] = (val >> 24) & 0xff;
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

int idris2_getBufferByte(void* buffer, int loc) {
    Buffer* b = buffer;
    if (loc >= 0 && loc < b->size) {
        return b->data[loc];
    } else {
        return 0;
    }
}

int idris2_getBufferInt(void* buffer, int loc) {
    Buffer* b = buffer;
    if (loc >= 0 && loc+3 < b->size) {
        return b->data[loc] +
               (b->data[loc+1] << 8) +
               (b->data[loc+2] << 16) +
               (b->data[loc+3] << 24);
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

void* idris2_readBufferFromFile(char* fn) {
    FILE* f = fopen(fn, "r");
    if (f == NULL) { return NULL; }

    int fd = fileno(f);
    int len;

    struct stat fbuf;
    if (fstat(fd, &fbuf) == 0) {
        len = (int)(fbuf.st_size);
    } else {
        return NULL;
    }

    size_t size = sizeof(Buffer) + len*sizeof(uint8_t);
    Buffer* buf = malloc(size);
    buf->size = len;

    fread((buf->data), sizeof(uint8_t), (size_t)len, f);
    fclose(f);
    return buf;
}

int idris2_writeBufferToFile(char* fn, void* buffer, int max) {
    Buffer* b = buffer;
    FILE* f = fopen(fn, "w");
    if (f == NULL) { return 0; }

    fwrite((b->data), sizeof(uint8_t), max, f);
    fclose(f);
    return -1;
}

// To be added when the file API has moved to the C support libs
/*
int idris2_readBuffer(FILE* h, void* buffer, int loc, int max) {
    Buffer* b = buffer;
    size_t len;

    if (loc >= 0 && loc < b->size) {
        if (loc + max > b->size) {
            max = b->size - loc;
        }
        len = fread((b->data)+loc, sizeof(uint8_t), (size_t)max, h);
        return len;
    } else {
        return 0;
    }
}

void idris2_writeBuffer(FILE* h, void* buffer, int loc, int len) {
    Buffer* b = buffer;

    if (loc >= 0 && loc < b->size) {
        if (loc + len > b->size) {
            len = b->size - loc;
        }
        fwrite((b->data)+loc, sizeof(uint8_t), len, h);
    }
}
*/
