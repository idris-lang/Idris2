const support_system_directory_fs = require("fs");

function support_system_directory_changeDir(d){
  try{
    process.chdir(d)
    return 0
  }catch(e){
    process.__lasterr = e
    return 1
  }
}

function support_system_directory_createDir(d){
  try{
    support_system_directory_fs.mkdirSync(d)
    return 0
  }catch(e){
    process.__lasterr = e
    return 1
  }
}

function support_system_directory_removeDir(d){
  try{
    support_system_directory_fs.rmdirSync(d)
    return 0
  }catch(e){
    process.__lasterr = e
    return 1
  }
}

function support_system_directory_openDir(d) {
  try{
    return support_system_directory_fs.opendirSync(d)
  }catch(e){
    process.__lasterr = e
    return null
  }
}

function support_system_directory_closeDir(d) {
  try{
    d.closeSync()
  }catch(e){
    process.__lasterr = e
    return null
  }
}

function support_system_directory_dirEntry(d) {
  try{
    const dir = d.readSync()
    if (dir == null) {
      return null
    } else {
      return dir.name
    }
  }catch(e){
    process.__lasterr = e
    return null
  }
}
