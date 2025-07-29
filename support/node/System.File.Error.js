// See System/File/Error.idr for return values
export function prim__fileErrno() {
  const n = process.__lasterr === undefined ? 0 : process.__lasterr.errno || 0
  if (process.platform == 'win32') {
    switch (n) {
      // these are documented in include/uv/errno.h of libuv
      case -4058: return 2
      case -4048: return 3
      case -4075: return 4
      default: return -n + 5
    }
  } else {
    switch (n) {
      case -2: return 2
      case -13: return 3
      case -17: return 4
      default: return -n + 5
    }
  }
}
