const support_system_file_fs = require('fs')
const support_system_file_child_process = require('child_process')

function support_system_file_fileErrno(){
  const n = process.__lasterr===undefined?0:process.__lasterr.errno || 0
  if (process.platform == 'win32') {
    // TODO: Add the error codes for the other errors
    switch(n) {
      case -4058: return 2
      case -4075: return 4
      default: return -n
    }
  } else {
    switch(n){
      case -17: return 4
      default: return -n
    }
  }
}

// like `readLine` without the overhead of copying characters.
// returns int (success 0, failure -1) to align with the C counterpart.
function support_system_file_seekLine (file_ptr) {
  const LF = 0x0a
  const readBuf = Buffer.alloc(1)
  let lineEnd = file_ptr.buffer.indexOf(LF)
  while (lineEnd === -1) {
    const bytesRead = support_system_file_fs.readSync(file_ptr.fd, readBuf, 0, 1, null)
    if (bytesRead === 0) {
      file_ptr.eof = true
      file_ptr.buffer = Buffer.alloc(0)
      return 0
    }
    file_ptr.buffer = Buffer.concat([file_ptr.buffer, readBuf.slice(0, bytesRead)])
    lineEnd = file_ptr.buffer.indexOf(LF)
  }
  file_ptr.buffer = file_ptr.buffer.slice(lineEnd + 1)
  return 0
}

function support_system_file_readLine (file_ptr) {
  const LF = 0x0a
  const readBuf = Buffer.alloc(1)
  let lineEnd = file_ptr.buffer.indexOf(LF)
  while (lineEnd === -1) {
    const bytesRead = support_system_file_fs.readSync(file_ptr.fd, readBuf, 0, 1, null)
    if (bytesRead === 0) {
      file_ptr.eof = true
      const line = file_ptr.buffer.toString('utf-8')
      file_ptr.buffer = Buffer.alloc(0)
      return line
    }
    file_ptr.buffer = Buffer.concat([file_ptr.buffer, readBuf.slice(0, bytesRead)])
    lineEnd = file_ptr.buffer.indexOf(LF)
  }
  const line = file_ptr.buffer.slice(0, lineEnd + 1).toString('utf-8')
  file_ptr.buffer = file_ptr.buffer.slice(lineEnd + 1)
  return line
}

function support_system_file_getStr () {
  return support_system_file_readLine({ fd: 0, buffer: Buffer.alloc(0), name: '<stdin>', eof: false })
}

function support_system_file_getChar() {
  const readBuf = Buffer.alloc(1);
  if (support_system_file_fs.readSync(process.stdin.fd, readBuf, 0, 1) === 0) {
    // No bytes read, getChar from libc returns -1 in this case.
    return String.fromCharCode(-1)
  } else {
    return readBuf.toString('utf-8')
  }
}

function support_system_file_parseMode(mode) {
  return mode.replace('b', '')
}

function support_system_file_openFile (n, m) {
  try {
    const fd = support_system_file_fs.openSync(n, support_system_file_parseMode(m))
    return { fd: fd, buffer: Buffer.alloc(0), name: n, eof: false }
  } catch (e) {
    process.__lasterr = e
    return null
  }
}

function support_system_file_chmod (filename, mode) {
  try {
    support_system_file_fs.chmodSync(filename, mode)
    return 0
  } catch (e) {
    process.__lasterr = e
    return 1
  }
}

function support_system_file_removeFile (filename) {
  try {
    support_system_file_fs.unlinkSync(filename)
    return 0
  } catch (e) {
    process.__lasterr = e
    return 1
  }
}

// IMPLEMENTATION NOTE:
// If in the future Idris's NodeJS backend supports executing async code, the
// far superior and more true-to-C way to implement popen/pclose would be to
// spawn in popen (instead of spawnSync) and then in pclose await the processes
// completion.
//
// Note doing the above makes it impossible to support the use-case for popen of
// writing to the child process's stdin between popen and pclose.
function support_system_file_popen (cmd, m) {
  const mode = support_system_file_parseMode(m)
  if (mode != 'r') {
    process.__lasterr = 'The NodeJS popen FFI only supports opening for reading currently.'
    return null
  }

  const tmp_file = require('os').tmpdir() + "/" + require('crypto').randomBytes(15).toString('hex')
  const write_fd = support_system_file_fs.openSync(
    tmp_file,
    'w'
  )

  var io_setting
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

  const { status, error  } = support_system_file_child_process.spawnSync(
    cmd,
    [],
    { stdio: io_setting, shell: true }
  )

  support_system_file_fs.closeSync(write_fd)

  if (error) {
    process.__lasterr = error
    return null
  }

  const read_ptr = support_system_file_openFile(
    tmp_file,
    'r'
  )

  return { ...read_ptr, exit_code: status }
}

function support_system_file_pclose (file_ptr) {
  const { fd, name, exit_code } = file_ptr
  support_system_file_fs.closeSync(fd)
  support_system_file_removeFile(name)
  return exit_code
}

function support_system_file_filetime(file_ptr) {
  const {fd, name, exit_code} = file_ptr
  const st = support_system_file_fs.fstatSync(fd)
  const ft = {
    atime_sec : _truncInt32(Math.trunc(st.atimeMs / 1000)),
    atime_nsec : st.atimeMs * 1000000 % 1000000000,
    mtime_sec : _truncInt32(Math.trunc(st.mtimeMs / 1000)),
    mtime_nsec : st.mtimeMs * 1000000 % 1000000000,
    ctime_sec : _truncInt32(Math.trunc(st.ctimeMs / 1000)),
    ctime_nsec : st.mtimeMs * 1000000 % 1000000000
  };
  return ft
}
