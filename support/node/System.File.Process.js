import fs from 'node:fs';
import os from 'node:os';
import crypto from 'node:crypto';
import child_process from 'node:child_process';
import { prim__removeFile } from './System.File.ReadWrite.js'
import { prim__open } from './System.File.Handle.js'
import { parseMode } from './utils.js'

// IMPLEMENTATION NOTE:
// If in the future Idris's NodeJS backend supports executing async code, the
// far superior and more true-to-C way to implement popen/pclose would be to
// spawn in popen (instead of spawnSync) and then in pclose await the processes
// completion.
//
// Note doing the above makes it impossible to support the use-case for popen of
// writing to the child process's stdin between popen and pclose.
export function prim__popen(cmd, m) {
  const mode = parseMode(m)
  if (mode != 'r') {
    process.__lasterr = 'The NodeJS popen FFI only supports opening for reading currently.'
    return null
  }

  const tmp_file = os.tmpdir() + "/" + crypto.randomBytes(15).toString('hex')
  const write_fd = fs.openSync(
    tmp_file,
    'w'
  )

  let io_setting
  switch (mode) {
    case "r":
      io_setting = ['ignore', write_fd, 2]
      break
    case "w":
    case "a":
      io_setting = [write_fd, 'ignore', 2]
      break
    default:
      process.__lasterr = 'The popen function cannot be used for reading and writing simultaneously.'
      return null
  }

  const { status, error } = child_process.spawnSync(
    cmd,
    [],
    { stdio: io_setting, shell: true }
  )

  fs.closeSync(write_fd)

  if (error) {
    process.__lasterr = error
    return null
  }

  const read_ptr = prim__open(
    tmp_file,
    'r'
  )

  return { ...read_ptr, exit_code: status }
}

export function prim__pclose(file_ptr) {
  const { fd, name, exit_code } = file_ptr
  fs.closeSync(fd)
  prim__removeFile(name)
  return exit_code
}
