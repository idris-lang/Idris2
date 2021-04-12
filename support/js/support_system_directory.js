const support_system_directory_fs = require("fs");

function support_system_directory_changeDir(d){
  try{
    process.chdir(d);
    return 0n
  }catch(e){
    process.__lasterr = e;
    return 1n
  }
}

function support_system_directory_createDir(d){
  try{
    support_system_directory_fs.mkdirSync(d)
    return 0n
  }catch(e){
    process.__lasterr = e;
    return 1n
  }
}
