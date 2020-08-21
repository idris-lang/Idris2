#ifndef _IDRIS_READLINE_H
#define _IDRIS_READLINE_H

void idrisrl_setCompletion(rl_completion_func_t* fn);

char* getString(void* str);
void* mkString(char* str);
void* nullString();
int isNullString(void* str);

#endif
