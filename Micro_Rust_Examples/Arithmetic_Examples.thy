(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Arithmetic_Examples
  imports
    Micro_Rust_Std_Lib.StdLib_Arithmetic
begin
(*>*)

section\<open>Worked examples: saturating and wrapping arithmetic\<close>

text\<open>This theory shows the saturating and wrapping arithmetic functions of
\<^theory>\<open>Micro_Rust_Std_Lib.StdLib_Arithmetic\<close> in use. Each example is a small \<^verbatim>\<open>\<mu>Rust\<close>
function that calls the library operations, paired with a contract and a one-line proof that
reuses the registered \<^verbatim>\<open>crush_specs\<close>. The examples are deliberately close to the
bounds-reasoning and modular-arithmetic patterns that arise in cryptographic code such as the
\<^verbatim>\<open>MLKEM\<close> development in this session.

All functions here are pure: they touch no heap, so the preconditions are \<^term>\<open>\<top>\<close> and the
proofs close with \<^verbatim>\<open>crush_boot\<close> + \<^verbatim>\<open>crush_base\<close>.\<close>

subsection\<open>Saturating arithmetic: overflow-safe bounds\<close>

text\<open>Saturating arithmetic is the natural tool for \<^emph>\<open>bounds that must never wrap\<close>. The
canonical example is a remaining-capacity computation: subtracting the number of used slots
from a capacity must never underflow below \<^term>\<open>0\<close>, otherwise a wrapped value would look like a
huge remaining capacity. \<^verbatim>\<open>saturating_sub\<close> clamps this to \<^term>\<open>0\<close>.\<close>

definition remaining_capacity :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>remaining_capacity capacity used \<equiv> FunctionBody \<lbrakk>
     capacity.saturating_sub(used)
  \<rbrakk>\<close>

definition remaining_capacity_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>remaining_capacity_contract capacity used \<equiv>
    let pre = \<top> in
    let post = \<lambda>ret. \<langle>ret = (if capacity < used then 0 else capacity - used)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto remaining_capacity_contract

lemma remaining_capacity_spec:
  shows \<open>\<Gamma> ; remaining_capacity capacity used \<Turnstile>\<^sub>F remaining_capacity_contract capacity used\<close>
by (crush_boot f: remaining_capacity_def contract: remaining_capacity_contract_def) crush_base

text\<open>Dually, accumulating a running total with \<^verbatim>\<open>saturating_add\<close> guarantees the counter never
overflows past \<^term>\<open>(- 1) :: 'l::len word\<close> (\<^verbatim>\<open>MAX\<close>); the result is pinned to \<^verbatim>\<open>MAX\<close> instead of
wrapping back towards \<^term>\<open>0\<close>. Here two increments are applied in sequence, and the
postcondition is the exact nested saturation.\<close>

definition bounded_counter_add2 :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>bounded_counter_add2 counter d1 d2 \<equiv> FunctionBody \<lbrakk>
     let c1 = counter.saturating_add(d1);
     return c1.saturating_add(d2);
  \<rbrakk>\<close>

definition bounded_counter_add2_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>bounded_counter_add2_contract counter d1 d2 \<equiv>
    let pre = \<top> in
    let post = \<lambda>ret. \<langle>ret = word_add_saturating_core (word_add_saturating_core counter d1) d2\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto bounded_counter_add2_contract

lemma bounded_counter_add2_spec:
  shows \<open>\<Gamma> ; bounded_counter_add2 counter d1 d2 \<Turnstile>\<^sub>F bounded_counter_add2_contract counter d1 d2\<close>
by (crush_boot f: bounded_counter_add2_def contract: bounded_counter_add2_contract_def)
  (crush_base simp add: word_add_saturating_core_def)

subsection\<open>Wrapping arithmetic: modular combinations\<close>

text\<open>Wrapping arithmetic is the right tool when the modular result is the \<^emph>\<open>intended\<close> value,
as in cryptographic coefficient arithmetic. A multiply–accumulate \<^verbatim>\<open>a * b + c\<close> computed
modulo \<^term>\<open>2 ^ LENGTH('l::len)\<close> is a recurring kernel; it composes \<^verbatim>\<open>wrapping_mul_unsigned\<close>
and \<^verbatim>\<open>wrapping_add_unsigned\<close> and the postcondition is the exact modular value, with no
clamping.\<close>

definition wrapping_mul_add :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>wrapping_mul_add a b c \<equiv> FunctionBody \<lbrakk>
     let p = a.wrapping_mul_unsigned(b);
     return p.wrapping_add_unsigned(c);
  \<rbrakk>\<close>

definition wrapping_mul_add_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wrapping_mul_add_contract a b c \<equiv>
    let pre = \<top> in
    let post = \<lambda>ret. \<langle>ret = a * b + c\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto wrapping_mul_add_contract

lemma wrapping_mul_add_spec:
  shows \<open>\<Gamma> ; wrapping_mul_add a b c \<Turnstile>\<^sub>F wrapping_mul_add_contract a b c\<close>
by (crush_boot f: wrapping_mul_add_def contract: wrapping_mul_add_contract_def) crush_base

text\<open>A difference of products \<^verbatim>\<open>a * b - c * d\<close> modulo \<^term>\<open>2 ^ LENGTH('l::len)\<close> exercises both
\<^verbatim>\<open>wrapping_mul_unsigned\<close> and \<^verbatim>\<open>wrapping_sub_unsigned\<close>; the subtraction may underflow, and
the wrapping semantics yields the modular difference with no separate case analysis.\<close>

definition wrapping_cross_diff :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>wrapping_cross_diff a b c d \<equiv> FunctionBody \<lbrakk>
     let p = a.wrapping_mul_unsigned(b);
     let q = c.wrapping_mul_unsigned(d);
     return p.wrapping_sub_unsigned(q);
  \<rbrakk>\<close>

definition wrapping_cross_diff_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wrapping_cross_diff_contract a b c d \<equiv>
    let pre = \<top> in
    let post = \<lambda>ret. \<langle>ret = a * b - c * d\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto wrapping_cross_diff_contract

lemma wrapping_cross_diff_spec:
  shows \<open>\<Gamma> ; wrapping_cross_diff a b c d \<Turnstile>\<^sub>F wrapping_cross_diff_contract a b c d\<close>
by (crush_boot f: wrapping_cross_diff_def contract: wrapping_cross_diff_contract_def) crush_base

subsection\<open>Mixing the families\<close>

text\<open>The two families coexist in one expression. The following clamps a modular index
computation back into a valid range: a wrapping multiply-accumulate produces a (possibly
wrapped) offset, and a \<^verbatim>\<open>saturating_sub\<close> against a length yields the distance to the end of a
buffer without ever underflowing. This mirrors the bounds bookkeeping that surrounds modular
coefficient arithmetic.\<close>

definition wrapping_then_saturating :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>wrapping_then_saturating buf_len a b c \<equiv> FunctionBody \<lbrakk>
     let offset = a.wrapping_mul_unsigned(b).wrapping_add_unsigned(c);
     return buf_len.saturating_sub(offset);
  \<rbrakk>\<close>

definition wrapping_then_saturating_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wrapping_then_saturating_contract buf_len a b c \<equiv>
    let pre = \<top> in
    let post = \<lambda>ret. \<langle>ret = (let offset = a * b + c in if buf_len < offset then 0 else buf_len - offset)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto wrapping_then_saturating_contract

lemma wrapping_then_saturating_spec:
  shows \<open>\<Gamma> ; wrapping_then_saturating buf_len a b c \<Turnstile>\<^sub>F wrapping_then_saturating_contract buf_len a b c\<close>
by (crush_boot f: wrapping_then_saturating_def contract: wrapping_then_saturating_contract_def) crush_base

(*<*)
end
(*>*)
