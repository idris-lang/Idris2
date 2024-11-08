export function prim__fileErrno() {
  const n = process.__lasterr === undefined ? 0 : process.__lasterr.errno || 0
  if (process.platform == 'win32') {
    // TODO: Add the error codes for the other errors
    switch (n) {
      case -4058: return 2
      case -4075: return 4
      default: return -n
    }
  } else {
    switch (n) {
      case -17: return 4
      default: return -n
    }
  }
}
