#ifndef _IDRIS_READLINE_H
#define _IDRIS_READLINE_H

#include <readline/readline.h>

void idris2_setCompletion(rl_completion_func_t* fn);

void* idris2_mkString(char* str);
void* idris2_nullString();
int idris2_isNullString(void* str);

#endif
