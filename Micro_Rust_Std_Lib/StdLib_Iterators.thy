(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Iterators
  imports Crush.Crush StdLib_References
begin
(*>*)

\<comment>\<open>Force one-by-one unrolling of loops\<close>
declare raw_for_loop_unroll_once_cong[crush_cong]

definition find ::
  \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
   ('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where
  \<open>find self predicate \<equiv> FunctionBody \<lbrakk>
    for x in self {
      if predicate(x) { return Some(x); }
    };
    None
  \<rbrakk>\<close>

definition enumerate :: \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
      ('s, ('s, 64 word \<times> 'v \<times> tnil, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>enumerate self \<equiv> FunctionBody (literal (make_iterator (mapi (\<lambda>i f. FunctionBody \<lbrakk>
      let feval = f();
      (\<llangle>word_of_nat i\<rrangle>, feval)
    \<rbrakk>) (iterator_thunks self))))\<close>

definition any :: \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
    ('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
    ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>any self predicate \<equiv> FunctionBody \<lbrakk>
     match self.find(predicate) {
       Some(_) \<Rightarrow> True,
       None    \<Rightarrow> False
     }
   \<rbrakk>\<close>

definition count :: \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
      ('s, 64 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count self \<equiv> FunctionBody \<lbrakk>
    \<llangle>of_nat \<circ> length \<circ> iterator_thunks\<rrangle>\<^sub>1(self)
   \<rbrakk>\<close>


context reference
begin

definition iter_mut ::
  \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> ('s, ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where
  \<open>iter_mut ref \<equiv> FunctionBody \<lbrakk>
    let xs = *ref;
    \<llangle>make_iterator_from_list (List.map (\<lambda>i. (focus_nth i ref)) [0 ..< length xs])\<rrangle>
  \<rbrakk>\<close>

(*<*)
end
(*>*)

subsection\<open>Debug printing\<close>

instantiation iterator :: (type, type, type, type, type)generate_debug
begin

definition generate_debug_iterator :: \<open>('a, 'b, 'c, 'd, 'e) iterator \<Rightarrow> log_data\<close> where
  \<open>generate_debug_iterator i \<equiv> [str ''<Iterator (length ='', LogNat (iterator_len i), str ''>'']\<close>

instance ..

end





declare lift_pure_to_contract_def [crush_contracts]
ucincl_auto lift_pure_to_contract

subsection\<open>Iterator fold\<close>

text\<open>Folds an accumulator over an iterator. This is the key combinator for expressing
loop-based computations as a single functional expression.
Uses monadic sequencing (no mutable references required).\<close>

text\<open>Recursive helper: fold over a list of thunks with an accumulator.\<close>
fun fold_thunks ::
  \<open>('s, 'a, 'r, 'abort, 'i prompt, 'o prompt_output) expression list \<Rightarrow>
   'b \<Rightarrow>
   ('b \<Rightarrow> 'a \<Rightarrow> ('s, 'b, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   ('s, 'b, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  where
  \<open>fold_thunks [] init f = literal init\<close>
| \<open>fold_thunks (thunk # thunks) init f =
    bind thunk (\<lambda>val_a.
      bind (call (f init val_a)) (\<lambda>new_acc.
        fold_thunks thunks new_acc f))\<close>

definition iterator_fold_func ::
  \<open>('s, 'a, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
   'b \<Rightarrow>
   ('b \<Rightarrow> 'a \<Rightarrow> ('s, 'b, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   ('s, 'b, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where
  \<open>iterator_fold_func self init f \<equiv> FunctionBody (
    fold_thunks (iterator_ethunks self) init f)\<close>

definition iterator_fold_contract where
  \<open>iterator_fold_contract vs init f_pure \<Gamma> f_rust \<equiv>
    let pre = \<langle>\<forall> acc v. \<Gamma>; f_rust acc v \<Turnstile>\<^sub>F lift_pure_to_contract (f_pure acc v)\<rangle> in
    let post = \<lambda> ret. \<langle>ret = foldl f_pure init vs\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto iterator_fold_contract

lemma iterator_fold_spec:
  shows \<open>\<Gamma> ; iterator_fold_func (make_iterator_from_list vs) init f_rust \<Turnstile>\<^sub>F iterator_fold_contract vs init f_pure \<Gamma> f_rust\<close>
proof (crush_boot f: iterator_fold_func_def contract: iterator_fold_contract_def, goal_cases)
  case 1
  note f_spec = this[THEN spec, THEN spec]
  show ?case proof (induct vs arbitrary: init)
    case Nil
    then show ?case
      by (crush_base simp add: make_iterator_from_list_def iterator_ethunks_def)
  next
    case (Cons v vs)
    note IH = this
    show ?case
      apply (crush_base simp add: make_iterator_from_list_def iterator_ethunks_def
                        specs add: f_spec)
      by (simp only: foldl.simps, rule IH)
  qed
qed

subsection\<open>Iterator map\<close>

text\<open>We define @{text map_thunks} with an accumulator to keep the structure tail-recursive,
mirroring the fold proof pattern. This ensures the induction hypothesis applies directly
after @{text crush_base} processes the first element.\<close>

fun map_thunks ::
  \<open>('s, 'a, 'r, 'abort, 'i prompt, 'o prompt_output) expression list \<Rightarrow>
   ('a \<Rightarrow> ('s, 'b, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   'b list \<Rightarrow>
   ('s, 'b list, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  where
  \<open>map_thunks [] f acc = literal acc\<close>
| \<open>map_thunks (thunk # thunks) f acc =
    bind thunk (\<lambda>val_a.
      bind (call (f val_a)) (\<lambda>result.
        map_thunks thunks f (acc @ [result])))\<close>

definition iterator_map ::
  \<open>('s, 'a, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
   ('a \<Rightarrow> ('s, 'b, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   ('s, 'b list, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where
  \<open>iterator_map self f \<equiv> FunctionBody (
    map_thunks (iterator_ethunks self) f [])\<close>

definition iterator_map_contract where
  \<open>iterator_map_contract vs f_pure \<Gamma> f_rust \<equiv>
    let pre = \<langle>\<forall> i. \<Gamma>; f_rust i \<Turnstile>\<^sub>F lift_pure_to_contract (f_pure i)\<rangle> in
    let post = \<lambda> ret. \<langle>ret = List.map f_pure vs\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto iterator_map_contract

lemma map_thunks_wp:
  assumes f_spec: \<open>\<And>i. \<Gamma>; f_rust i \<Turnstile>\<^sub>F lift_pure_to_contract (f_pure i)\<close>
  shows \<open>UNIV \<longlongrightarrow> \<W>\<P> \<Gamma> (map_thunks (List.map literal vs) f_rust acc)
    (\<lambda>ret. \<langle>ret = acc @ List.map f_pure vs\<rangle>)
    (\<lambda>ret. \<langle>ret = acc @ List.map f_pure vs\<rangle>) \<bottom>\<close>
proof (induct vs arbitrary: acc)
  case Nil
  show ?case by crush_base
next
  case (Cons v vs)
  note IH = Cons.hyps
  show ?case
    apply (crush_base specs add: f_spec)
    \<comment>\<open>After crush_base, goal has acc @{text "@"} [f_pure v] as new accumulator but
       postcondition mentions @{text "acc @ map f_pure (v # vs)"}. The IH with the
       right accumulator matches after simplification.\<close>
    using IH[where acc=\<open>acc @ [f_pure v]\<close>] by simp
qed

lemma iterator_map_spec:
  shows \<open>\<Gamma> ; iterator_map (make_iterator_from_list vs) f_rust \<Turnstile>\<^sub>F iterator_map_contract vs f_pure \<Gamma> f_rust\<close>
proof (crush_boot f: iterator_map_def contract: iterator_map_contract_def, goal_cases)
  case 1
  note f_spec = this[THEN spec]
  have wp: \<open>UNIV \<longlongrightarrow> \<W>\<P> \<Gamma> (map_thunks (List.map literal vs) f_rust [])
    (\<lambda>ret. \<langle>ret = List.map f_pure vs\<rangle>)
    (\<lambda>ret. \<langle>ret = List.map f_pure vs\<rangle>) \<bottom>\<close>
    using map_thunks_wp[OF f_spec, where acc=\<open>[]\<close>] by simp
  show ?case
    by (crush_base simp add: make_iterator_from_list_def iterator_ethunks_def
                   wp intro add: wp)
qed

subsection\<open>Iterator filter\<close>

text\<open>Filters elements of an iterator by a predicate, collecting matching elements into a list.
Uses an accumulator for a tail-recursive structure that mirrors the fold/map proof pattern.\<close>

fun filter_thunks ::
  \<open>('s, 'a, 'r, 'abort, 'i prompt, 'o prompt_output) expression list \<Rightarrow>
   ('a \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   'a list \<Rightarrow>
   ('s, 'a list, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  where
  \<open>filter_thunks [] pred acc = literal acc\<close>
| \<open>filter_thunks (thunk # thunks) pred acc =
    bind thunk (\<lambda>val_a.
      bind (call (pred val_a)) (\<lambda>keep.
        filter_thunks thunks pred (if keep then acc @ [val_a] else acc)))\<close>

definition iterator_filter_func ::
  \<open>('s, 'a, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
   ('a \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   ('s, 'a list, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where
  \<open>iterator_filter_func self pred \<equiv> FunctionBody (
    filter_thunks (iterator_ethunks self) pred [])\<close>

definition iterator_filter_contract where
  \<open>iterator_filter_contract vs pred_pure \<Gamma> pred_rust \<equiv>
    let pre = \<langle>\<forall> i. \<Gamma>; pred_rust i \<Turnstile>\<^sub>F lift_pure_to_contract (pred_pure i)\<rangle> in
    let post = \<lambda> ret. \<langle>ret = List.filter pred_pure vs\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto iterator_filter_contract

lemma filter_thunks_wp:
  assumes pred_spec: \<open>\<And>i. \<Gamma>; pred_rust i \<Turnstile>\<^sub>F lift_pure_to_contract (pred_pure i)\<close>
  shows \<open>UNIV \<longlongrightarrow> \<W>\<P> \<Gamma> (filter_thunks (List.map literal vs) pred_rust acc)
    (\<lambda>ret. \<langle>ret = acc @ List.filter pred_pure vs\<rangle>)
    (\<lambda>ret. \<langle>ret = acc @ List.filter pred_pure vs\<rangle>) \<bottom>\<close>
proof (induct vs arbitrary: acc)
  case Nil
  show ?case by crush_base
next
  case (Cons v vs)
  note IH = Cons.hyps
  show ?case
    apply (crush_base specs add: pred_spec split!: if_splits)
    subgoal premises prems
    proof -
      \<comment>\<open>False branch: accumulator unchanged, filter skips v\<close>
      from prems have eq: \<open>filter pred_pure (v # vs) = filter pred_pure vs\<close> by simp
      show ?thesis using IH[where acc=\<open>acc\<close>] by (simp only: eq)
    qed
    subgoal premises prems
    proof -
      \<comment>\<open>True branch: accumulator gets v appended\<close>
      from prems have eq: \<open>acc @ filter pred_pure (v # vs) = (acc @ [v]) @ filter pred_pure vs\<close> by simp
      show ?thesis using IH[where acc=\<open>acc @ [v]\<close>] by (simp only: eq)
    qed
    done
qed

lemma iterator_filter_spec:
  shows \<open>\<Gamma> ; iterator_filter_func (make_iterator_from_list vs) pred_rust \<Turnstile>\<^sub>F iterator_filter_contract vs pred_pure \<Gamma> pred_rust\<close>
proof (crush_boot f: iterator_filter_func_def contract: iterator_filter_contract_def, goal_cases)
  case 1
  note pred_spec = this[THEN spec]
  have wp: \<open>UNIV \<longlongrightarrow> \<W>\<P> \<Gamma> (filter_thunks (List.map literal vs) pred_rust [])
    (\<lambda>ret. \<langle>ret = List.filter pred_pure vs\<rangle>)
    (\<lambda>ret. \<langle>ret = List.filter pred_pure vs\<rangle>) \<bottom>\<close>
    using filter_thunks_wp[OF pred_spec, where acc=\<open>[]\<close>] by simp
  show ?case
    by (crush_base simp add: make_iterator_from_list_def iterator_ethunks_def
                   wp intro add: wp)
qed

subsection\<open>Find contract and spec\<close>

definition iterator_find_contract :: \<open>'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>
  ('machine::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('a \<Rightarrow> ('machine, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('machine, 'a option, 'abort) function_contract\<close> where
  \<open>iterator_find_contract vs pred_pure \<Gamma> pred_rust \<equiv>
    let pre = \<langle>\<forall> i. \<Gamma>; pred_rust i \<Turnstile>\<^sub>F lift_pure_to_contract (pred_pure i)\<rangle> in
    let post = \<lambda> ret. \<langle>ret = List.find pred_pure vs\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto iterator_find_contract

lemma iterator_find_spec:
  shows \<open>\<Gamma> ; StdLib_Iterators.find (make_iterator_from_list vs) pred_rust \<Turnstile>\<^sub>F iterator_find_contract vs pred_pure \<Gamma> pred_rust\<close>
proof (crush_boot f: StdLib_Iterators.find_def contract: iterator_find_contract_def, goal_cases)
  case 1
  note pred_spec = this[THEN spec]
  show ?case proof (crush_base inline: iterator_into_iter_def, induction vs)
    case Nil
    then show ?case
      by (crush_base simp add: raw_for_loop_def)
  next
    case (Cons a vs)
    note IH = this
    show ?case
      apply (crush_base specs add: pred_spec)
      apply (cases \<open>pred_pure a\<close>)
       apply crush_base
      apply (subst List.find.simps(2), simp)
      by (rule IH)
  qed
qed

(*<*)
end
(*>*)
