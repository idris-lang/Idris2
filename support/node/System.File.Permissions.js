import fs from 'node:fs';

export function prim__chmod(filename, mode) {
  try {
    fs.chmodSync(filename, mode)
    return 0
  } catch (e) {
    process.__lasterr = e
    return 1
  }
}
