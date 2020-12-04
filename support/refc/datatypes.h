#ifndef __DATATYPES_H__
#define __DATATYPES_H__
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdint.h>

#define NO_TAG 0
#define INT8_TAG 1
#define INT16_TAG 2
#define INT32_TAG 3
#define INT64_TAG 4
#define DOUBLE_TAG 5
#define CHAR_TAG 6
#define STRING_TAG 7

#define CLOSURE_TAG 10
#define ARGLIST_TAG 11
#define CONSTRUCTOR_TAG 12

#define IOREF_TAG 20
#define ARRAY_TAG 21
#define POINTER_TAG 22
#define GC_POINTER_TAG 23
#define BUFFER_TAG 24

#define MUTEX_TAG 30
#define CONDITION_TAG 31

#define COMPLETE_CLOSURE_TAG 98 // for trampoline tail recursion handling
#define WORLD_TAG 99

typedef struct
{
    int refCounter;
    int tag;
} Value_header;

typedef struct
{
    Value_header header;
    char payload[25];
} Value;

typedef struct
{
    Value_header header;
    uint8_t i8;
} Value_Int8;

typedef struct
{
    Value_header header;
    uint16_t i16;
} Value_Int16;

typedef struct
{
    Value_header header;
    int32_t i32;
} Value_Int32;

typedef struct
{
    Value_header header;
    int64_t i64;
} Value_Int64;

typedef struct
{
    Value_header header;
    double d;
} Value_Double;

typedef struct
{
    Value_header header;
    char c;
} Value_Char;

typedef struct
{
    Value_header header;
    char *str;
} Value_String;

typedef struct
{
    Value_header header;
    int32_t total;
    int32_t tag;
    char *name;
    Value **args;
} Value_Constructor;

typedef struct
{
    Value_header header;
    int32_t total;
    int32_t filled;
    Value **args;
} Value_Arglist;

typedef Value *(*fun_ptr_t)(Value_Arglist *);

typedef struct
{
    Value_header header;
    fun_ptr_t f;
    Value_Arglist *arglist;
} Value_Closure;

typedef struct
{
    Value_header header;
    int32_t index;
} Value_IORef;

typedef struct
{
    Value_header header;
    void *p;
} Value_Pointer;

typedef struct
{
    Value_header header;
    Value_Pointer *p;
    Value_Closure *onCollectFct;
} Value_GCPointer;

typedef struct
{
    Value_header header;
    int capacity;
    Value **arr;
} Value_Array;

typedef struct
{
    Value_header header;
    size_t len;
    char *buffer;
} Value_Buffer;

typedef struct
{
    Value_header header;
    pthread_mutex_t *mutex;
} Value_Mutex;

typedef struct
{
    Value_header header;
    pthread_cond_t *cond;
} Value_Condition;

typedef struct
{
    Value **refs;
    int filled;
    int total;
} IORef_Storage;

typedef struct
{
    Value_header header;
    IORef_Storage *listIORefs;
} Value_World;

#endif
