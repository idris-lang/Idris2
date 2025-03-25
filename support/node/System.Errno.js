export function prim__getErrno() {
  return process.__lasterr === undefined ? 0 : -process.__lasterr.errno || 0
}
