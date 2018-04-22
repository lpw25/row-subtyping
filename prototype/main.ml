
module StringMap = Map.Make(String)

let directives_list =
  ["quit", fun () -> exit 0]

let directives =
  List.fold_left
    (fun acc (dir, fn) ->
      StringMap.add dir fn acc)
    StringMap.empty
    directives_list

let run_directive dir =
  match StringMap.find dir directives with
  | fn -> fn ()
  | exception Not_found ->
      Format.printf "Unknown directive: %s.@." dir

let prompt = "# "

let read_interactive_input first buffer len =
  if first then begin
    output_string Pervasives.stdout prompt;
    flush Pervasives.stdout
  end;
  let i = ref 0 in
  try
    while true do
      if !i >= len then raise Exit;
      let c = input_char Pervasives.stdin in
      Bytes.set buffer !i c;
      incr i;
      if c = '\n' then raise Exit;
    done;
    (!i, false)
  with
  | End_of_file ->
      (!i, true)
  | Exit ->
      (!i, false)

let first_line = ref true
let got_eof = ref false;;

let refill_lexbuf buffer len =
  if !got_eof then begin
    got_eof := false; 0
  end else begin
    let (len, eof) = read_interactive_input !first_line buffer len in
    first_line := false;
    if eof then begin
      output_string Pervasives.stdout "End of file";
      flush Pervasives.stdout;
      if len > 0 then got_eof := true;
      len
    end else begin
      len
    end
  end

let loop () =
  Format.printf "        Row Subtyping@.";
  let lb = Lexing.from_function refill_lexbuf in
  Sys.catch_break true;
  while true do
    try
      Lexing.flush_input lb;
      first_line := true;
      let phrase = Parser.phrase Lexer.token lb in
      match phrase with
      | Expr expr ->
          Format.printf "@[<v 2>Parsed:@ %a@]@." Ast.dump_expr expr
      | Directive dir ->
          run_directive dir
    with
    | End_of_file -> exit 0
    | Sys.Break -> Format.printf "Interrupted.@."
  done

let () =
  loop ()
