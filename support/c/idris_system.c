#include <stdlib.h>
#include "idris_system.h"

int idris2_system(const char* command) {
    return system(command);
}
