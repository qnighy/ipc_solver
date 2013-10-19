
let sprintf fmt =
  let buf = Buffer.create 100 in
  let f = Format.formatter_of_buffer buf in
  Format.kfprintf (fun f ->
    Format.pp_print_flush f ();
    Buffer.contents buf
  ) f fmt
