open OUnit2
open Enigma

(** [index_test name input expected_output] constructs an OUnit test
    named [name] that asserts the quality of [expected_output] with
    [index input]. *)
let index_test (name : string) (input : char) (expected_output : int) :
    test =
  name >:: fun _ ->
  (* the [printer] tells OUnit how to convert the output to a string *)
  assert_equal expected_output (index input) ~printer:string_of_int

(* You will find it helpful to write functions like [index_test] for
   each of the other functions you are testing. They will keep your
   lists of tests below very readable, and will also help you to avoid
   repeating code. You will also find it helpful to create [~printer]
   functions for the data types in use. *)

let index_tests =
  [ index_test "index of A is 0" 'A' 0 (* TODO: add your tests here *) ]

let map_rl_tests = [ (* TODO: add your tests here *) ]

let map_lr_tests = [ (* TODO: add your tests here *) ]

let map_refl_tests = [ (* TODO: add your tests here *) ]

let map_plug_tests = [ (* TODO: add your tests here *) ]

let cipher_char_tests = [ (* TODO: add your tests here *) ]

let step_tests = [ (* TODO: add your tests here *) ]

let cipher_tests = [ (* TODO: add your tests here *) ]

let tests =
  "test suite for A1"
  >::: List.flatten
         [
           index_tests;
           map_rl_tests;
           map_lr_tests;
           map_refl_tests;
           map_plug_tests;
           cipher_char_tests;
           step_tests;
           cipher_tests;
         ]

let _ = run_test_tt_main tests
