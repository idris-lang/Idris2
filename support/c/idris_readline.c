#include <stdlib.h>
#include <stdio.h>
#include <string.h>

/*
 * Bare minimum readline support.
 * Supported functions: readline, add_history, idris2_setCompletion
 * If READLINE is not set, dummy functions are used in their place.
 */

#ifdef READLINE

#include <readline/readline.h>

rl_compentry_func_t* my_compentry = NULL;

char* compentry_wrapper(const char* text, int i) {
    char* res = my_compentry(text, i); // Idris frees this
    if (res != NULL) {
        char* comp = malloc(strlen(res)+1); // Readline frees this
        strcpy(comp, res);
        return comp;
    }
    else {
        return NULL;
    }
}

void idris2_setCompletion(rl_compentry_func_t* fn) {
    rl_completion_entry_function = compentry_wrapper;
    my_compentry = fn;
}

#else

void idris2_setCompletion(void* fn) {}

char* readline(char *prompt) {
  char* buf = NULL;
  size_t len = 0;
  printf("%s", prompt);
  ssize_t linesize = getline(&buf, &len, stdin);
  if (linesize >= 1 && buf[linesize - 1] == '\n') {
    buf[linesize - 1] = '\0';
    #if defined(WIN32) || defined(WIN64)
    if (linesize >= 2 && buf[linesize - 2] == '\r') {
      buf[linesize - 2] = '\0';
    }
    #endif
  }
  if (feof(stdin)) {
    free(buf);
    return NULL;
  }
  return buf;
}

void add_history(char* line) {}

#endif

void* idris2_mkString(char* str) {
    return (void*)str;
}

void* idris2_nullString() {
    return NULL;
}

int idris2_isNullString(void* str) {
    return str == NULL;
}
