(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Ordering
  imports Crush.Crush StdLib_References Misc.Result
begin
(*>*)

datatype ordering
  = Less
  | Equal
  | Greater
notation_nano_rust ordering.Less ("Ordering::Less")
notation_nano_rust ordering.Equal ("Ordering::Equal")
notation_nano_rust ordering.Greater ("Ordering::Greater")

definition cmp_pure :: \<open>'a::{order} \<Rightarrow> 'a \<Rightarrow> ordering\<close> where
  \<open>cmp_pure x y \<equiv>
     if x < y then
       Less
     else if x = y then
       Equal
     else Greater\<close>

definition cmp :: \<open>'a::{order} \<Rightarrow> 'a \<Rightarrow> ('s, ordering, 'abort, 'i, 'o) function_body\<close> where
  \<open>cmp \<equiv> lift_fun2 cmp_pure\<close>

(*
 * Function definition for ordering equality
 *)

definition is_eq_pure :: \<open>ordering  \<Rightarrow> bool\<close> where
  \<open>is_eq_pure x \<equiv>
    if x = Equal then True else False\<close>

definition is_eq :: \<open>ordering \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>is_eq \<equiv> lift_fun1 is_eq_pure\<close>

(*
 * Contract definition and proof
 *)

definition eq_test where \<open>eq_test \<equiv> FunctionBody \<lbrakk>
    let mut nat_ref_1 = \<llangle>0 :: 64 word\<rrangle>;
    let mut nat_ref_2 = \<llangle>0 :: 64 word\<rrangle>;
    let mut bool_ref_result = \<llangle>True :: bool\<rrangle>;
    let mut temp_order = \<llangle>Equal :: ordering\<rrangle>;
    temp_order = cmp(*nat_ref_1, *nat_ref_2);
    bool_ref_result = is_eq(*temp_order);
    *bool_ref_result
  \<rbrakk>\<close>

definition eq_test_contract where
  \<open>eq_test_contract \<equiv>
     let pre  = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = True\<rangle> in
     make_function_contract pre post\<close>
ucincl_auto eq_test_contract

lemma eq_test_spec:
  shows \<open>\<Gamma>; eq_test \<Turnstile>\<^sub>F eq_test_contract\<close>
  apply (crush_boot f: eq_test_def contract: eq_test_contract_def)
  apply crush_base
  sorry


(*<*)
end
(*>*)