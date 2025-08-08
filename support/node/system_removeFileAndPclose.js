import fs from 'node:fs';

export function prim__removeFile(filename) {
  try {
    fs.unlinkSync(filename)
    return 0
  } catch (e) {
    process.__lasterr = e
    return 1
  }
}

export function prim__pclose(file_ptr) {
  const { fd, name, exit_code } = file_ptr
  fs.closeSync(fd)
  prim__removeFile(name)
  return exit_code
}
