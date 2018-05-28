
module StringMap = Map.Make(String)

let last_scheme = ref None

let quit () =
  exit 0

let raw () =
  match !last_scheme with
  | None -> ()
  | Some scheme ->
      Types.Printing.print_raw_scheme scheme;
      Format.printf "\n%!"

let directives_list =
  [ "quit", quit;
    "raw", raw ]

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

let highlight_location lb start_pos end_pos =
  let open Lexing in
  (* Char 0 is at offset -lb.lex_abs_pos in lb.lex_buffer. *)
  let cnum0 = -lb.lex_abs_pos in
  (* Do nothing if the buffer does not contain the whole phrase. *)
  if cnum0 < 0 then raise Exit;
  let end_cnum = lb.lex_buffer_len - cnum0 - 1 in
  (* Determine line numbers for the start and end points *)
  let line_start = ref 0 and line_end = ref 0 in
  for cnum = 0 to end_cnum do
    if Bytes.get lb.lex_buffer (cnum + cnum0) = '\n' then begin
      if start_pos.pos_cnum > cnum then incr line_start;
      if end_pos.pos_cnum > cnum then incr line_end;
    end
  done;
  Format.printf "@[<v>";
  (* Print the input, underlining the location *)
  Format.print_string "  ";
  let line = ref 0 in
  let cnum_at_bol = ref 0 in
  for cnum = 0 to end_cnum do
    match Bytes.get lb.lex_buffer (cnum + cnum0) with
    | '\n' ->
      if !line = !line_start && !line = !line_end then begin
        (* loc is on one line: underline location *)
        Format.printf "@,  ";
        for _i = !cnum_at_bol to start_pos.pos_cnum - 1 do
          Format.print_char ' '
        done;
        for _i = start_pos.pos_cnum to end_pos.pos_cnum - 1 do
          Format.print_char '^'
        done
      end;
      if !line >= !line_start && !line <= !line_end then begin
        Format.printf "@,";
        if cnum < end_pos.pos_cnum then Format.print_string "  "
      end;
      incr line;
      cnum_at_bol := cnum + 1
    | '\r' -> () (* discard *)
    | c ->
      if !line = !line_start && !line = !line_end then
        (* loc is on one line: print whole line *)
        Format.print_char c
      else if !line = !line_start then
        (* first line of multiline loc:
           print a dot for each char before start_pos *)
        if cnum < start_pos.pos_cnum then
          Format.print_char '.'
        else
          Format.print_char c
      else if !line = !line_end then
        (* last line of multiline loc: print a dot for each char
           after end_pos, even whitespaces *)
        if cnum < end_pos.pos_cnum then
          Format.print_char c
        else
          Format.print_char '.'
      else if !line > !line_start && !line < !line_end then
        (* intermediate line of multiline loc: print whole line *)
        Format.print_char c
  done;
  Format.printf "@]%!"

let rec skip_phrase lexbuf =
  try
    match Lexer.token lexbuf with
    | Parser.SEMISEMI -> ()
    | _ -> skip_phrase lexbuf
  with
  | Lexer.Error _ -> skip_phrase lexbuf

let start_pos =
  { Lexing.pos_fname = "*REPL*";
    pos_lnum = 1;
    pos_bol = 0;
    pos_cnum = 0; }

let main () =
  Format.printf "        Row Subtyping@.";
  let lb = Lexing.from_function refill_lexbuf in
  lb.lex_curr_p <- start_pos;
  let supplier =
    Parser.MenhirInterpreter.lexer_lexbuf_to_supplier Lexer.token lb
  in
  let start = Parser.Incremental.phrase start_pos in
  Sys.catch_break true;
  let rec loop env =
    match
      Lexing.flush_input lb;
      first_line := true;
      let phrase =
        Parser.MenhirInterpreter.loop_handle
          (fun phrase -> Ok phrase)
          (fun checkpoint ->
             match checkpoint with
             | HandlingError env -> Error env
             | _ -> assert false)
          supplier start
      in
      match phrase with
      | Ok phrase -> begin
          match phrase.desc with
          | Statement { statement } -> begin
              let name =
                match statement.desc with
                | Definition { binding } -> begin
                    match binding with
                    | Unnamed -> "_"
                    | Named { name; location } -> name
                  end
                | Expr _ -> "_"
              in
              match Infer.infer env statement with
              | env, scheme ->
                  Format.printf "%s : " name;
                  Types.Printing.print_scheme scheme;
                  Format.printf "\n%!";
                  last_scheme := Some scheme;
                  env
              | exception Infer.Error(loc, Typing(t1, t2, err)) ->
                  Types.Printing.print_unification_error t1 t2 err;
                  Format.printf "\n\n%!";
                  highlight_location lb loc.start_pos loc.end_pos;
                  env
              | exception Infer.Error(loc, Binding name) ->
                  Format.printf "Error: unbound variable %s\n\n%!" name;
                  highlight_location lb loc.start_pos loc.end_pos;
                  env
            end
          | Directive { directive } ->
              run_directive directive;
              env
        end
      | Error menv ->
          let start_pos, end_pos = Parser.MenhirInterpreter.positions menv in
          let state = Parser.MenhirInterpreter.current_state_number menv in
          let msg = ParserMessages.message state in
          Format.printf "Error: %s\n%!" msg;
          highlight_location lb start_pos end_pos;
          skip_phrase lb;
          env
    with
    | exception End_of_file -> exit 0
    | exception Sys.Break ->
        Format.printf "Interrupted.@.";
        loop env
    | exception Lexer.Error (Lexer.Illegal_character c, pos) ->
        Format.printf "Error: illegal character %c\n\n%!" c;
        highlight_location lb pos pos;
        skip_phrase lb;
        loop env
    | env -> loop env
  in
  loop Types.Env.empty

let () =
  main ()
