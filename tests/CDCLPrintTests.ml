



open Printf
let printEachTest t = 
  let () = List.iter (printf "%c") t in printf "\n"

let () = List.iter printEachTest CDCLTests.runTests