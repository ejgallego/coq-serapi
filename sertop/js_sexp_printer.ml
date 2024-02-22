(** Emilio J. Gallego Arias: Code below is adapted from Jane Street's
    sexplib, licence is:

The MIT License

Copyright (c) 2005--2024 Jane Street Group, LLC opensource-contacts@janestreet.com

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)

open Format
open Sexplib
open Sexp

let must_escape str =
  let len = String.length str in
  len = 0 ||
    let rec loop ix =
      match str.[ix] with
      | '"' | '(' | ')' | '[' | ']' | ';' | '\\' | '\''-> true
      (* Avoid unquoted comma at the beggining of the string *)
      | ',' -> ix = 0 || loop (ix - 1)
      | '|' -> ix > 0 && let next = ix - 1 in str.[next] = '#' || loop next
      | '#' -> ix > 0 && let next = ix - 1 in str.[next] = '|' || loop next
      | '\000' .. '\032' -> true
      | '\248' .. '\255' -> true
      | _ -> ix > 0 && loop (ix - 1)
    in
    loop (len - 1)

(* XXX: Be faithful to UTF-8 *)
let st_escaped (s : string) =
  let sget = String.unsafe_get in
  let open Bytes in
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    n := !n +
      (match sget s i with
       | '\"' | '\\' | '\n' | '\t' | '\r' | '\b' -> 2
       | ' ' .. '~' -> 1
       (* UTF-8 are valid between \033 -- \247 *)
       | '\000' .. '\032' -> 4
       | '\248' .. '\255' -> 4
       | _                -> 1)
  done;
  if !n = String.length s then Bytes.of_string s else begin
    let s' = create !n in
    n := 0;
    for i = 0 to String.length s - 1 do
      begin match sget s i with
      | ('\"' | '\\') as c ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n c
      | '\n' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'n'
      | '\t' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 't'
      | '\r' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'r'
      | '\b' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'b'
      | (' ' .. '~') as c -> unsafe_set s' !n c
      (* Valid UTF-8 are valid between \033 -- \247 *)
      | '\000' .. '\032'
      | '\248' .. '\255' as c ->
          let a = Char.code c in
          unsafe_set s' !n '\\';
          incr n;
          unsafe_set s' !n (Char.chr (48 + a / 100));
          incr n;
          unsafe_set s' !n (Char.chr (48 + (a / 10) mod 10));
          incr n;
          unsafe_set s' !n (Char.chr (48 + a mod 10));
      | c -> unsafe_set s' !n c
      end;
      incr n
    done;
    s'
  end

let esc_str (str : string) =
  let open Bytes in
  let estr = st_escaped str in
  let elen = length estr in
  let res  = create (elen + 2) in
  blit estr 0 res 1 elen;
  set res 0 '"';
  set res (elen + 1) '"';
  to_string res

let sertop_maybe_esc_str str =
  if must_escape str then esc_str str else str

let rec pp_sertop_internal may_need_space ppf = function
  | Atom str ->
      let str' = sertop_maybe_esc_str str in
      let new_may_need_space = str' == str in
      if may_need_space && new_may_need_space then pp_print_string ppf " ";
      pp_print_string ppf str';
      new_may_need_space
  | List (h :: t) ->
      pp_print_string ppf "(";
      let may_need_space = pp_sertop_internal false ppf h in
      pp_sertop_rest may_need_space ppf t;
      false
  | List [] -> pp_print_string ppf "()"; false

and pp_sertop_rest may_need_space ppf = function
  | h :: t ->
      let may_need_space = pp_sertop_internal may_need_space ppf h in
      pp_sertop_rest may_need_space ppf t
  | [] -> pp_print_string ppf ")"

let pp_sertop ppf sexp = ignore (pp_sertop_internal false ppf sexp)
