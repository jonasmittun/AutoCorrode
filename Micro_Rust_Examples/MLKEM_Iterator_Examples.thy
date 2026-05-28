(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory MLKEM_Iterator_Examples
  imports
    MLKEM_Specification
    Micro_Rust_Std_Lib.StdLib_All
    Crush.Crush
begin

text\<open>
  Demonstrations of MLKEM-style operations expressed using the verified iterator
  combinators @{const iterator_map}, @{const iterator_fold_func}, and
  @{const iterator_filter_func}. These show how loop-based cryptographic computations
  can be expressed compositionally and verified against pure specifications.
\<close>

section\<open>Locale\<close>

locale mlkem_iterator_context =
    reference reference_types +
    ref_word16: reference_allocatable reference_types _ _ _ _ _ _ _ word16_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
      'o prompt_output \<Rightarrow> unit\<close>
  and word16_prism :: \<open>('gv, 16 word) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word16.new

section\<open>Pure specifications\<close>

definition poly_coeff_sum_pure :: \<open>16 word list \<Rightarrow> 16 word\<close> where
  \<open>poly_coeff_sum_pure coeffs \<equiv> foldl zq_add 0 coeffs\<close>

definition poly_scalar_mul_pure :: \<open>16 word \<Rightarrow> 16 word list \<Rightarrow> 16 word list\<close> where
  \<open>poly_scalar_mul_pure c coeffs \<equiv> List.map (\<lambda>x. zq_mul c x) coeffs\<close>

definition poly_filter_nonzero_pure :: \<open>16 word list \<Rightarrow> 16 word list\<close> where
  \<open>poly_filter_nonzero_pure coeffs \<equiv> List.filter (\<lambda>x. x \<noteq> 0) coeffs\<close>

section\<open>Polynomial coefficient sum via fold\<close>

text\<open>Sums all polynomial coefficients mod q using @{const iterator_fold_func}.
This pattern is common in cryptographic hash computations and checksum operations.\<close>

definition zq_add_rust :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
    ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>zq_add_rust acc x \<equiv> FunctionBody \<lbrakk>
    \<llangle>zq_add acc x\<rrangle>
  \<rbrakk>\<close>

definition zq_add_rust_contract :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
    ('s::{sepalg}, 16 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>zq_add_rust_contract acc x \<equiv>
    make_function_contract \<top> (\<lambda>r. \<langle>r = zq_add acc x\<rangle>)\<close>
ucincl_auto zq_add_rust_contract

lemma zq_add_rust_spec [crush_specs]:
  shows \<open>\<Gamma>; zq_add_rust acc x \<Turnstile>\<^sub>F zq_add_rust_contract acc x\<close>
  by (crush_boot f: zq_add_rust_def contract: zq_add_rust_contract_def) crush_base

lemma zq_add_rust_satisfies_lift:
  shows \<open>\<Gamma>; zq_add_rust acc x \<Turnstile>\<^sub>F lift_pure_to_contract (zq_add acc x)\<close>
  using zq_add_rust_spec
  by (simp add: zq_add_rust_contract_def lift_pure_to_contract_def)

definition poly_coeff_sum :: \<open>16 word list \<Rightarrow>
    ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_coeff_sum coeffs \<equiv>
    iterator_fold_func (make_iterator_from_list coeffs) 0 zq_add_rust\<close>

definition poly_coeff_sum_contract where
  [crush_contracts]: \<open>poly_coeff_sum_contract coeffs \<equiv>
    iterator_fold_contract coeffs 0 zq_add \<Gamma> zq_add_rust\<close>
ucincl_auto poly_coeff_sum_contract

lemma poly_coeff_sum_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_coeff_sum coeffs \<Turnstile>\<^sub>F poly_coeff_sum_contract coeffs\<close>
  unfolding poly_coeff_sum_def poly_coeff_sum_contract_def
  by (rule iterator_fold_spec)

section\<open>Polynomial scalar multiplication via map\<close>

text\<open>Multiplies each coefficient by a scalar mod q using @{const iterator_map}.
This pattern appears in MLKEM's polynomial-by-scalar operations.\<close>

definition zq_scalar_mul_rust :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
    ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>zq_scalar_mul_rust c x \<equiv> FunctionBody \<lbrakk>
    \<llangle>zq_mul c x\<rrangle>
  \<rbrakk>\<close>

definition zq_scalar_mul_rust_contract :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
    ('s::{sepalg}, 16 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>zq_scalar_mul_rust_contract c x \<equiv>
    make_function_contract \<top> (\<lambda>r. \<langle>r = zq_mul c x\<rangle>)\<close>
ucincl_auto zq_scalar_mul_rust_contract

lemma zq_scalar_mul_rust_spec [crush_specs]:
  shows \<open>\<Gamma>; zq_scalar_mul_rust c x \<Turnstile>\<^sub>F zq_scalar_mul_rust_contract c x\<close>
  by (crush_boot f: zq_scalar_mul_rust_def contract: zq_scalar_mul_rust_contract_def) crush_base

lemma zq_scalar_mul_rust_satisfies_lift:
  shows \<open>\<Gamma>; zq_scalar_mul_rust c x \<Turnstile>\<^sub>F lift_pure_to_contract (zq_mul c x)\<close>
  using zq_scalar_mul_rust_spec
  by (simp add: zq_scalar_mul_rust_contract_def lift_pure_to_contract_def)

definition poly_scalar_mul :: \<open>16 word \<Rightarrow> 16 word list \<Rightarrow>
    ('s, 16 word list, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_scalar_mul c coeffs \<equiv>
    iterator_map (make_iterator_from_list coeffs) (zq_scalar_mul_rust c)\<close>

definition poly_scalar_mul_contract where
  [crush_contracts]: \<open>poly_scalar_mul_contract c coeffs \<equiv>
    iterator_map_contract coeffs (zq_mul c) \<Gamma> (zq_scalar_mul_rust c)\<close>
ucincl_auto poly_scalar_mul_contract

lemma poly_scalar_mul_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_scalar_mul c coeffs \<Turnstile>\<^sub>F poly_scalar_mul_contract c coeffs\<close>
  unfolding poly_scalar_mul_def poly_scalar_mul_contract_def
  by (rule iterator_map_spec)

section\<open>Filter non-zero coefficients\<close>

text\<open>Collects non-zero coefficients using @{const iterator_filter_func}.
This pattern is useful for sparse polynomial representations and
for extracting non-trivial terms during NTT computations.\<close>

definition nonzero_pred_rust :: \<open>16 word \<Rightarrow>
    ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>nonzero_pred_rust x \<equiv> FunctionBody \<lbrakk>
    \<llangle>x \<noteq> 0\<rrangle>
  \<rbrakk>\<close>

definition nonzero_pred_contract :: \<open>16 word \<Rightarrow>
    ('s::{sepalg}, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>nonzero_pred_contract x \<equiv>
    make_function_contract \<top> (\<lambda>r. \<langle>r = (x \<noteq> 0)\<rangle>)\<close>
ucincl_auto nonzero_pred_contract

lemma nonzero_pred_rust_spec [crush_specs]:
  shows \<open>\<Gamma>; nonzero_pred_rust x \<Turnstile>\<^sub>F nonzero_pred_contract x\<close>
  by (crush_boot f: nonzero_pred_rust_def contract: nonzero_pred_contract_def) crush_base

lemma nonzero_pred_rust_satisfies_lift:
  shows \<open>\<Gamma>; nonzero_pred_rust x \<Turnstile>\<^sub>F lift_pure_to_contract (x \<noteq> 0)\<close>
  using nonzero_pred_rust_spec
  by (simp add: nonzero_pred_contract_def lift_pure_to_contract_def)

definition poly_filter_nonzero :: \<open>16 word list \<Rightarrow>
    ('s, 16 word list, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_filter_nonzero coeffs \<equiv>
    iterator_filter_func (make_iterator_from_list coeffs) nonzero_pred_rust\<close>

definition poly_filter_nonzero_contract where
  [crush_contracts]: \<open>poly_filter_nonzero_contract coeffs \<equiv>
    iterator_filter_contract coeffs (\<lambda>x. x \<noteq> 0) \<Gamma> nonzero_pred_rust\<close>
ucincl_auto poly_filter_nonzero_contract

lemma poly_filter_nonzero_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_filter_nonzero coeffs \<Turnstile>\<^sub>F poly_filter_nonzero_contract coeffs\<close>
  unfolding poly_filter_nonzero_def poly_filter_nonzero_contract_def
  by (rule iterator_filter_spec)

section\<open>Find first coefficient above threshold\<close>

text\<open>Finds the first coefficient exceeding a given threshold using @{const StdLib_Iterators.find}.
This pattern is relevant in MLKEM for detecting overflow conditions or
locating the first element failing a range check.\<close>

definition above_threshold_pred_rust :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
    ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>above_threshold_pred_rust thresh x \<equiv> FunctionBody \<lbrakk>
    \<llangle>thresh < x\<rrangle>
  \<rbrakk>\<close>

definition above_threshold_pred_contract :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
    ('s::{sepalg}, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>above_threshold_pred_contract thresh x \<equiv>
    make_function_contract \<top> (\<lambda>r. \<langle>r = (thresh < x)\<rangle>)\<close>
ucincl_auto above_threshold_pred_contract

lemma above_threshold_pred_rust_spec [crush_specs]:
  shows \<open>\<Gamma>; above_threshold_pred_rust thresh x \<Turnstile>\<^sub>F above_threshold_pred_contract thresh x\<close>
  by (crush_boot f: above_threshold_pred_rust_def contract: above_threshold_pred_contract_def)
     crush_base

lemma above_threshold_pred_rust_satisfies_lift:
  shows \<open>\<Gamma>; above_threshold_pred_rust thresh x \<Turnstile>\<^sub>F lift_pure_to_contract (thresh < x)\<close>
  using above_threshold_pred_rust_spec
  by (simp add: above_threshold_pred_contract_def lift_pure_to_contract_def)

definition poly_find_above_threshold :: \<open>16 word \<Rightarrow> 16 word list \<Rightarrow>
    ('s, 16 word option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_find_above_threshold thresh coeffs \<equiv>
    StdLib_Iterators.find (make_iterator_from_list coeffs) (above_threshold_pred_rust thresh)\<close>

definition poly_find_above_threshold_contract where
  [crush_contracts]: \<open>poly_find_above_threshold_contract thresh coeffs \<equiv>
    iterator_find_contract coeffs (\<lambda>x. thresh < x) \<Gamma> (above_threshold_pred_rust thresh)\<close>
ucincl_auto poly_find_above_threshold_contract

lemma poly_find_above_threshold_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_find_above_threshold thresh coeffs \<Turnstile>\<^sub>F poly_find_above_threshold_contract thresh coeffs\<close>
  unfolding poly_find_above_threshold_def poly_find_above_threshold_contract_def
  by (rule iterator_find_spec)

section\<open>Composed pipeline: scalar multiply then sum\<close>

text\<open>Computes @{term \<open>foldl zq_add 0 (map (zq_mul c) coeffs)\<close>} by first mapping
then folding. This models an inner-product contribution: multiply each coefficient
by a scalar, then sum the results. Demonstrates composing verified iterator combinators.\<close>

definition poly_scalar_dot_pure :: \<open>16 word \<Rightarrow> 16 word list \<Rightarrow> 16 word\<close> where
  \<open>poly_scalar_dot_pure c coeffs \<equiv> foldl zq_add 0 (List.map (zq_mul c) coeffs)\<close>

definition poly_scalar_dot :: \<open>16 word \<Rightarrow> 16 word list \<Rightarrow>
    ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_scalar_dot c coeffs \<equiv> FunctionBody \<lbrakk>
    let scaled = \<llangle>iterator_map (make_iterator_from_list coeffs) (zq_scalar_mul_rust c)\<rrangle>;
    \<llangle>iterator_fold_func (make_iterator_from_list scaled) 0 zq_add_rust\<rrangle>
  \<rbrakk>\<close>

definition poly_scalar_dot_contract where
  [crush_contracts]: \<open>poly_scalar_dot_contract c coeffs \<equiv>
    make_function_contract \<top> (\<lambda>r. \<langle>r = poly_scalar_dot_pure c coeffs\<rangle>)\<close>
ucincl_auto poly_scalar_dot_contract

lemma poly_scalar_dot_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_scalar_dot c coeffs \<Turnstile>\<^sub>F poly_scalar_dot_contract c coeffs\<close>
  unfolding poly_scalar_dot_contract_def
  by (crush_boot f: poly_scalar_dot_def contract: poly_scalar_dot_contract_def)
     (crush_base specs add: iterator_map_spec[where f_pure=\<open>zq_mul c\<close>]
                            iterator_fold_spec[where f_pure=zq_add]
                 simp add: poly_scalar_dot_pure_def
                           iterator_map_contract_def iterator_fold_contract_def
                           zq_scalar_mul_rust_satisfies_lift zq_add_rust_satisfies_lift)

section\<open>Composed pipeline: filter then count non-zero elements\<close>

text\<open>Counts the number of non-zero coefficients by filtering then computing the length
of the result. This pattern is useful for Hamming weight computations on coefficient
vectors in lattice-based cryptography.\<close>

definition poly_count_nonzero_pure :: \<open>16 word list \<Rightarrow> nat\<close> where
  \<open>poly_count_nonzero_pure coeffs \<equiv> length (List.filter (\<lambda>x. x \<noteq> 0) coeffs)\<close>

definition poly_count_nonzero :: \<open>16 word list \<Rightarrow>
    ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_count_nonzero coeffs \<equiv> FunctionBody \<lbrakk>
    let nonzeros = \<llangle>iterator_filter_func (make_iterator_from_list coeffs) nonzero_pred_rust\<rrangle>;
    \<llangle>length nonzeros\<rrangle>
  \<rbrakk>\<close>

definition poly_count_nonzero_contract where
  [crush_contracts]: \<open>poly_count_nonzero_contract coeffs \<equiv>
    make_function_contract \<top> (\<lambda>r. \<langle>r = poly_count_nonzero_pure coeffs\<rangle>)\<close>
ucincl_auto poly_count_nonzero_contract

lemma poly_count_nonzero_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_count_nonzero coeffs \<Turnstile>\<^sub>F poly_count_nonzero_contract coeffs\<close>
  unfolding poly_count_nonzero_contract_def
  by (crush_boot f: poly_count_nonzero_def contract: poly_count_nonzero_contract_def)
     (crush_base specs add: iterator_filter_spec[where pred_pure=\<open>\<lambda>x. x \<noteq> 0\<close>]
                 simp add: poly_count_nonzero_pure_def
                           iterator_filter_contract_def
                           nonzero_pred_rust_satisfies_lift)

end

end
