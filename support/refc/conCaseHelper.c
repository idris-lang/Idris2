#include "conCaseHelper.h"
#include "refc_util.h"

int multiStringCompare(Value *sc, int nrDecicionOptions, char **options) {
  for (int i = 0; i < nrDecicionOptions; i++) {
    if (!strcmp(((Value_String *)sc)->str, options[i])) {
      return i;
    }
  }
  return -1;
}

int multiDoubleCompare(Value *sc, int nrDecicionOptions, double *options) {
  for (int i = 0; i < nrDecicionOptions; i++) {
    if (((Value_Double *)sc)->d == options[i]) {
      return i;
    }
  }
  return -1;
}
