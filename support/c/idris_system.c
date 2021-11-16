#include <stdlib.h>
#include "idris_system.h"

int idris2_system(const char* command) {
    int status = system(command);
    #ifdef _WIN32
      return status;
    #else
      return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
    #endif
}
