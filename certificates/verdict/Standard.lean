import Verdict.Spec.PolicyStandard
import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.Iterators.Lemmas.Consumers.Loop

namespace VerdictCertificates.Standard
open Verdict.Policy Verdict.Policy.Standard

private theorem chrome_parts {env chain task}
    (h : Verdict.chromeValidChain env chain task = true) :
    chain.length ≥ 2 ∧
    Verdict.chromeCertVerifiedLeaf env task chain[0]! chain[chain.length - 1]! = true ∧
    ((List.range (chain.length - 2)).all fun d =>
      Verdict.chromeCertVerifiedIntermediate env task chain[d + 1]! d) = true ∧
    Verdict.chromeCertVerifiedRoot env task chain[chain.length - 1]!
      chain[chain.length - 2]! (chain.length - 2) = true ∧
    Verdict.chromeCheckAllNameConstraints chain = true := by
  simp only [Verdict.chromeValidChain, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

private theorem firefox_parts {env chain task}
    (h : Verdict.firefoxValidChain env chain task = true) :
    chain.length ≥ 2 ∧
    Verdict.firefoxCertVerifiedLeaf env task (chain.getD 0 default) false = true ∧
    ((List.range (chain.length - 2)).all fun d =>
      Verdict.firefoxCertVerifiedIntermediate env task (chain.getD (d + 1) default)
        (chain.getD 0 default) d) = true ∧
    Verdict.firefoxCertVerifiedRoot env task (chain.getD (chain.length - 1) default)
      (chain.getD (chain.length - 2) default) (chain.getD 0 default) (chain.length - 2) = true ∧
    Verdict.firefoxCheckAllNameConstraints chain = true := by
  simpa only [Verdict.firefoxValidChain, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] using h

private theorem openssl_parts {chain task}
    (h : Verdict.opensslValidChain chain task = true) :
    chain.length ≥ 2 ∧ Verdict.opensslValidLeaf task chain[0]! = true ∧
    ((List.range (chain.length - 2)).all fun d =>
      Verdict.opensslValidIntermediate task chain[d + 1]! d) = true ∧
    Verdict.opensslValidRoot task chain[chain.length - 1]! (chain.length - 2) = true ∧
    Verdict.opensslCheckNameConstraints chain = true ∧
    (match task.hostname with
      | none => true
      | some host => Verdict.opensslCheckHostname chain[0]! host) = true := by
  simpa only [Verdict.opensslValidChain, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] using h

private theorem chrome_all {env chain task} (Q : AbstractCertificate → Prop)
    (h : Verdict.chromeValidChain env chain task = true)
    (leaf : ∀ c r, Verdict.chromeCertVerifiedLeaf env task c r = true → Q c)
    (inter : ∀ c d, Verdict.chromeCertVerifiedIntermediate env task c d = true → Q c)
    (root : ∀ c r d, Verdict.chromeCertVerifiedRoot env task c r d = true → Q c) :
    ∀ i, i < chain.length → Q chain[i]! := by
  obtain ⟨hn, hl, hi, hr, _⟩ := chrome_parts h
  intro i hn'
  by_cases h0 : i = 0
  · subst i; exact leaf _ _ hl
  by_cases hr' : i = chain.length - 1
  · subst i; exact root _ _ _ hr
  have hd : i - 1 < chain.length - 2 := by omega
  have hi := List.all_eq_true.mp hi (i - 1) (List.mem_range.mpr hd)
  have he : i - 1 + 1 = i := by omega
  rw [he] at hi
  exact inter _ _ hi

private theorem firefox_all {env chain task} (Q : AbstractCertificate → Prop)
    (h : Verdict.firefoxValidChain env chain task = true)
    (leaf : ∀ c, Verdict.firefoxCertVerifiedLeaf env task c false = true → Q c)
    (inter : ∀ c l d, Verdict.firefoxCertVerifiedIntermediate env task c l d = true → Q c)
    (root : ∀ c r l d, Verdict.firefoxCertVerifiedRoot env task c r l d = true → Q c) :
    ∀ i, i < chain.length → Q chain[i]! := by
  obtain ⟨hn, hl, hi, hr, _⟩ := firefox_parts h
  intro i hn'
  simp only [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  by_cases h0 : i = 0
  · subst i; exact leaf _ hl
  by_cases hr' : i = chain.length - 1
  · subst i; exact root _ _ _ _ hr
  have hd : i - 1 < chain.length - 2 := by omega
  have hi := List.all_eq_true.mp hi (i - 1) (List.mem_range.mpr hd)
  have he : i - 1 + 1 = i := by omega
  rw [he] at hi
  exact inter _ _ _ hi

private theorem openssl_all {chain task} (Q : AbstractCertificate → Prop)
    (h : Verdict.opensslValidChain chain task = true)
    (leaf : ∀ c, Verdict.opensslValidLeaf task c = true → Q c)
    (inter : ∀ c d, Verdict.opensslValidIntermediate task c d = true → Q c)
    (root : ∀ c d, Verdict.opensslValidRoot task c d = true → Q c) :
    ∀ i, i < chain.length → Q chain[i]! := by
  obtain ⟨hn, hl, hi, hr, _⟩ := openssl_parts h
  intro i hn'
  by_cases h0 : i = 0
  · subst i; exact leaf _ hl
  by_cases hr' : i = chain.length - 1
  · subst i; exact root _ _ hr
  have hd : i - 1 < chain.length - 2 := by omega
  have hi := List.all_eq_true.mp hi (i - 1) (List.mem_range.mpr hd)
  have he : i - 1 + 1 = i := by omega
  rw [he] at hi
  exact inter _ _ hi

theorem chrome_chain_min_length :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    ChainMinLength (Verdict.chromeValidChain env) := by
  intro env chain task h; exact (chrome_parts h).1

theorem firefox_chain_min_length :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    ChainMinLength (Verdict.firefoxValidChain env) := by
  intro env chain task h; exact (firefox_parts h).1

theorem openssl_chain_min_length :
  ChainMinLength Verdict.opensslValidChain := by
  intro chain task h; exact (openssl_parts h).1

theorem chrome_name_constraints_respected :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    NameConstraintsRespected (Verdict.chromeValidChain env)
      Verdict.chromeCheckAllNameConstraints := by
  intro env chain task h; exact (chrome_parts h).2.2.2.2

theorem firefox_name_constraints_respected :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    NameConstraintsRespected (Verdict.firefoxValidChain env)
      Verdict.firefoxCheckAllNameConstraints := by
  intro env chain task h; exact (firefox_parts h).2.2.2.2

theorem openssl_name_constraints_respected :
  NameConstraintsRespected Verdict.opensslValidChain
    Verdict.opensslCheckNameConstraints := by
  intro chain task h; exact (openssl_parts h).2.2.2.2.1

theorem openssl_hostname_match :
  HostnameMatch Verdict.opensslValidChain Verdict.opensslCheckHostname := by
  intro chain task h _ host hh
  simpa only [hh] using (openssl_parts h).2.2.2.2.2

theorem chrome_unique_extensions :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    UniqueExtensions (Verdict.chromeValidChain env) := by
  intro env chain task h
  apply chrome_all (fun c => checkDuplicateExtensions c = true) h
  · intro c r hc; simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true] at hc; grind only
  · intro c d hc
    simp only [Verdict.chromeCertVerifiedIntermediate, Chrome.Reference.certVerifiedNonLeaf,
      Bool.and_eq_true] at hc
    grind only
  · intro c r d hc
    simp only [Verdict.chromeCertVerifiedRoot, Chrome.Reference.certVerifiedNonLeaf,
      Bool.and_eq_true] at hc
    grind only

theorem chrome_valid_pki :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    ValidPKI (Verdict.chromeValidChain env) Verdict.Policy.Chrome.isValidPki := by
  intro env chain task h
  apply chrome_all (fun c => Chrome.isValidPki c = true) h
  · intro c r hc; simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true] at hc; grind only
  · intro c d hc
    simp only [Verdict.chromeCertVerifiedIntermediate, Chrome.Reference.certVerifiedNonLeaf,
      Bool.and_eq_true] at hc
    grind only
  · intro c r d hc
    simp only [Verdict.chromeCertVerifiedRoot, Chrome.Reference.certVerifiedNonLeaf,
      Bool.and_eq_true] at hc
    grind only

theorem chrome_valid_version :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    ValidVersion (Verdict.chromeValidChain env) := by
  intro env chain task h
  have hv : ∀ i, i < chain.length → chain[i]!.version = 2 := by
    apply chrome_all (fun c => c.version = 2) h
    · intro c r hc
      simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true, beq_iff_eq] at hc
      grind only
    · intro c d hc
      simp only [Verdict.chromeCertVerifiedIntermediate, Chrome.Reference.certVerifiedNonLeaf,
        Bool.and_eq_true, beq_iff_eq] at hc
      grind only
    · intro c r d hc
      simp only [Verdict.chromeCertVerifiedRoot, Chrome.Reference.certVerifiedNonLeaf,
        Bool.and_eq_true, beq_iff_eq] at hc
      grind only
  intro i hi _; exact hv i hi

theorem firefox_unique_extensions :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    UniqueExtensions (Verdict.firefoxValidChain env) := by
  intro env chain task h
  apply firefox_all (fun c => checkDuplicateExtensions c = true) h
  · intro c hc; simp only [Verdict.firefoxCertVerifiedLeaf, Bool.and_eq_true] at hc; grind only
  · intro c l d hc
    simp only [Verdict.firefoxCertVerifiedIntermediate, Firefox.Reference.nonLeaf,
      Bool.and_eq_true] at hc
    grind only
  · intro c r l d hc
    simp only [Verdict.firefoxCertVerifiedRoot, Firefox.Reference.nonLeaf,
      Bool.and_eq_true] at hc
    grind only

theorem firefox_time_validity :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    TimeValidity (Verdict.firefoxValidChain env) := by
  intro env chain task h
  apply firefox_all (fun c => c.notBefore ≤ task.now ∧ task.now ≤ c.notAfter) h
  · intro c hc
    simp only [Verdict.firefoxCertVerifiedLeaf, Bool.and_eq_true, decide_eq_true_eq] at hc
    grind only
  · intro c l d hc
    simp only [Verdict.firefoxCertVerifiedIntermediate, Firefox.Reference.nonLeaf,
      Bool.and_eq_true, decide_eq_true_eq] at hc
    grind only
  · intro c r l d hc
    simp only [Verdict.firefoxCertVerifiedRoot, Firefox.Reference.nonLeaf,
      Bool.and_eq_true, decide_eq_true_eq] at hc
    grind only

theorem openssl_unique_extensions :
  UniqueExtensions Verdict.opensslValidChain := by
  intro chain task h
  apply openssl_all (fun c => checkDuplicateExtensions c = true) h <;> intros <;>
    simp_all only [Verdict.opensslValidLeaf, Verdict.opensslValidIntermediate,
      Verdict.opensslValidRoot, OpenSSL.validCertCommon, OpenSSL.checkDuplicateExts,
      Bool.and_eq_true] <;> grind only

theorem openssl_valid_pki :
  ValidPKI Verdict.opensslValidChain Verdict.Policy.OpenSSL.checkCertKeyLevel := by
  intro chain task h
  apply openssl_all (fun c => OpenSSL.checkCertKeyLevel c = true) h <;> intros <;>
    simp_all only [Verdict.opensslValidLeaf, Verdict.opensslValidIntermediate,
      Verdict.opensslValidRoot, OpenSSL.validCertCommon, Bool.and_eq_true] <;> grind only

theorem openssl_time_validity :
  TimeValidity Verdict.opensslValidChain := by
  intro chain task h
  apply openssl_all (fun c => c.notBefore ≤ task.now ∧ task.now ≤ c.notAfter) h <;> intros <;>
    simp_all only [Verdict.opensslValidLeaf, Verdict.opensslValidIntermediate,
      Verdict.opensslValidRoot, OpenSSL.validCertCommon, OpenSSL.checkCertTime,
      Bool.and_eq_true, decide_eq_true_eq] <;>
    grind only [UInt64.le_of_lt]

private theorem chrome_middle {env chain task i}
    (h : Verdict.chromeValidChain env chain task = true) (hi : 0 < i)
    (hn : i + 1 < chain.length) :
    Verdict.chromeCertVerifiedIntermediate env task chain[i]! (i - 1) = true := by
  have hh := List.all_eq_true.mp (chrome_parts h).2.2.1 (i - 1)
    (List.mem_range.mpr (by omega))
  simpa only [show i - 1 + 1 = i by omega] using hh

private theorem firefox_middle {env chain task i}
    (h : Verdict.firefoxValidChain env chain task = true) (hi : 0 < i)
    (hn : i + 1 < chain.length) :
    Verdict.firefoxCertVerifiedIntermediate env task chain[i]! chain[0]! (i - 1) = true := by
  have hh := List.all_eq_true.mp (firefox_parts h).2.2.1 (i - 1)
    (List.mem_range.mpr (by omega))
  simpa only [show i - 1 + 1 = i by omega, List.getElem!_eq_getElem?_getD,
    List.getD_eq_getElem?_getD] using hh

private theorem openssl_middle {chain task i}
    (h : Verdict.opensslValidChain chain task = true) (hi : 0 < i)
    (hn : i + 1 < chain.length) :
    Verdict.opensslValidIntermediate task chain[i]! (i - 1) = true := by
  have hh := List.all_eq_true.mp (openssl_parts h).2.2.1 (i - 1)
    (List.mem_range.mpr (by omega))
  simpa only [show i - 1 + 1 = i by omega] using hh

theorem chrome_time_validity :
  ∀ (env : Verdict.Policy.ChromePolicyEnv) chain task,
    Verdict.chromeValidChain env chain task = true →
    ∀ i, i + 1 < chain.length →
      chain[i]!.notBefore ≤ task.now ∧ task.now ≤ chain[i]!.notAfter := by
  intro env chain task h i hi
  by_cases hz : i = 0
  · subst i
    have hc := (chrome_parts h).2.1
    simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true, decide_eq_true_eq] at hc
    grind only
  · have hc := chrome_middle h (by omega : 0 < i) hi
    simp only [Verdict.chromeCertVerifiedIntermediate, Bool.and_eq_true, decide_eq_true_eq] at hc
    grind only

theorem chrome_basic_constraints_ca :
  ∀ (env : Verdict.Policy.ChromePolicyEnv) chain task,
    Verdict.chromeValidChain env chain task = true →
    ∀ i, 0 < i → i + 1 < chain.length →
      chain[i]!.extBasicConstraints.any (·.isCA) = true := by
  intro env chain task h i hi hn
  have hc := chrome_middle h hi hn
  generalize hc0 : chain[i]! = c at hc ⊢
  cases he : c.extBasicConstraints <;>
    simp [Verdict.chromeCertVerifiedIntermediate, he, Bool.and_eq_true] at hc ⊢
  grind only

private theorem chrome_nonleaf {env chain task} (Q : AbstractCertificate → Prop)
    (h : Verdict.chromeValidChain env chain task = true)
    (inter : ∀ c d, Verdict.chromeCertVerifiedIntermediate env task c d = true → Q c)
    (root : ∀ c r d, Verdict.chromeCertVerifiedRoot env task c r d = true → Q c) :
    ∀ i, 0 < i → i < chain.length → Q chain[i]! := by
  intro i hi hn
  by_cases he : i = chain.length - 1
  · subst i; exact root _ _ _ (chrome_parts h).2.2.2.1
  · exact inter _ _ (chrome_middle h hi (by omega))

private theorem firefox_nonleaf {env chain task} (Q : AbstractCertificate → Prop)
    (h : Verdict.firefoxValidChain env chain task = true)
    (inter : ∀ c l d, Verdict.firefoxCertVerifiedIntermediate env task c l d = true → Q c)
    (root : ∀ c r l d, Verdict.firefoxCertVerifiedRoot env task c r l d = true → Q c) :
    ∀ i, 0 < i → i < chain.length → Q chain[i]! := by
  intro i hi hn
  by_cases he : i = chain.length - 1
  · subst i
    simpa only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD] using
      root _ _ _ _ (firefox_parts h).2.2.2.1
  · exact inter _ _ _ (firefox_middle h hi (by omega))

private theorem openssl_nonleaf {chain task} (Q : AbstractCertificate → Prop)
    (h : Verdict.opensslValidChain chain task = true)
    (inter : ∀ c d, Verdict.opensslValidIntermediate task c d = true → Q c)
    (root : ∀ c d, Verdict.opensslValidRoot task c d = true → Q c) :
    ∀ i, 0 < i → i < chain.length → Q chain[i]! := by
  intro i hi hn
  by_cases he : i = chain.length - 1
  · subst i; exact root _ _ (openssl_parts h).2.2.2.1
  · exact inter _ _ (openssl_middle h hi (by omega))

theorem firefox_basic_constraints_ca :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    BasicConstraintsCA (Verdict.firefoxValidChain env) := by
  intro env chain task h
  apply firefox_nonleaf (fun c => c.extBasicConstraints.any (·.isCA) = true) h
  · intro c l d hc
    cases he : c.extBasicConstraints <;>
      simp [Verdict.firefoxCertVerifiedIntermediate, Firefox.Reference.nonLeaf,
        he, Bool.and_eq_true] at hc ⊢
    grind only
  · intro c r l d hc
    cases he : c.extBasicConstraints <;>
      simp [Verdict.firefoxCertVerifiedRoot, Firefox.Reference.nonLeaf,
        he, Bool.and_eq_true] at hc ⊢
    grind only

private theorem chrome_inter_ku {env task c d}
    (hc : Verdict.chromeCertVerifiedIntermediate env task c d = true) :
    match c.extKeyUsage with | some ku => ku.keyCertSign = true | none => True := by
  cases hb : c.extBasicConstraints <;> cases hk : c.extKeyUsage <;>
    simp [Verdict.chromeCertVerifiedIntermediate, Chrome.keyUsageValid, hb, hk,
      Bool.and_eq_true] at hc ⊢
  split at hc <;> simp_all

theorem chrome_key_usage_ca :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    KeyUsageCA (Verdict.chromeValidChain env) := by
  intro env chain task h
  apply chrome_nonleaf (fun c => match c.extKeyUsage with
    | some ku => ku.keyCertSign = true | none => True) h
  · intro c d hc; exact chrome_inter_ku hc
  · intro c r d hc
    cases hk : c.extKeyUsage <;>
      simp [Verdict.chromeCertVerifiedRoot, hk, Bool.and_eq_true] at hc ⊢
    grind only

theorem firefox_key_usage_ca :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    KeyUsageCA (Verdict.firefoxValidChain env) := by
  intro env chain task h
  apply firefox_nonleaf (fun c => match c.extKeyUsage with
    | some ku => ku.keyCertSign = true | none => True) h
  · intro c l d hc
    cases hk : c.extKeyUsage <;>
      simp [Verdict.firefoxCertVerifiedIntermediate, Firefox.Reference.nonLeaf,
        Firefox.checkKeyUsageIntermediate, hk, Bool.and_eq_true] at hc ⊢
    grind only
  · intro c r l d hc
    cases hk : c.extKeyUsage <;>
      simp [Verdict.firefoxCertVerifiedRoot, Firefox.Reference.nonLeaf,
        Firefox.checkKeyUsageIntermediate, hk, Bool.and_eq_true] at hc ⊢
    grind only

theorem firefox_key_usage_leaf :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    KeyUsageLeaf (Verdict.firefoxValidChain env) := by
  intro env chain task h _
  have hc := (firefox_parts h).2.1
  simp only [List.getD_eq_getElem?_getD, ← List.getElem!_eq_getElem?_getD] at hc
  generalize hc0 : chain[0]! = c at hc ⊢
  cases hk : c.extKeyUsage <;>
    simp [Verdict.firefoxCertVerifiedLeaf, Firefox.checkKeyUsageLeaf, hk,
      Bool.and_eq_true] at hc ⊢
  grind only

theorem firefox_extended_key_usage_leaf :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    ExtendedKeyUsageLeaf (Verdict.firefoxValidChain env) := by
  intro env chain task h _
  have hc := (firefox_parts h).2.1
  simp only [List.getD_eq_getElem?_getD, ← List.getElem!_eq_getElem?_getD] at hc
  generalize hc0 : chain[0]! = c at hc ⊢
  cases hk : c.extExtendedKeyUsage <;>
    simp [Verdict.firefoxCertVerifiedLeaf, Firefox.Reference.extendedKeyUsage, hk,
      Bool.and_eq_true, List.contains_eq_any_beq] at hc ⊢
  grind only

theorem chrome_path_length_enforced :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    PathLengthEnforced (Verdict.chromeValidChain env) := by
  intro env chain task h i hi hn
  have hc := chrome_middle h hi hn
  generalize he : chain[i]! = c at hc ⊢
  cases hb : c.extBasicConstraints with
  | none => simp [hb]
  | some bc =>
    cases hp : bc.pathLen with
    | none => simp [hb, hp]
    | some pl =>
      simp only [Verdict.chromeCertVerifiedIntermediate, Chrome.Reference.certVerifiedNonLeaf,
        hb, hp, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [hb, hp]
      have hpl : 0 ≤ pl ∧ i - 1 ≤ pl.toNat := by grind only
      have hn : (i - 1 : Int) = ((i - 1 : Nat) : Int) := by omega
      rw [hn]
      omega

theorem firefox_path_length_enforced :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    PathLengthEnforced (Verdict.firefoxValidChain env) := by
  intro env chain task h i hi hn
  have hc := firefox_middle h hi hn
  generalize he : chain[i]! = c at hc ⊢
  cases hb : c.extBasicConstraints with
  | none => simp [hb]
  | some bc =>
    cases hp : bc.pathLen with
    | none => simp [hb, hp]
    | some pl =>
      simp only [Verdict.firefoxCertVerifiedIntermediate, Firefox.Reference.nonLeaf,
        hb, hp, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [hb, hp]
      have hpl : ((i - 1 : Nat) : Int) ≤ pl := by grind only
      omega

theorem openssl_path_length_enforced :
  PathLengthEnforced Verdict.opensslValidChain := by
  intro chain task h i hi hn
  have hc := openssl_middle h hi hn
  generalize he : chain[i]! = c at hc ⊢
  cases hb : c.extBasicConstraints with
  | none => simp [hb]
  | some bc =>
    cases hp : bc.pathLen with
    | none => simp [hb, hp]
    | some pl =>
      simp only [Verdict.opensslValidIntermediate, OpenSSL.validCertCommon,
        hb, hp, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [hb, hp]
      have hpl : ((i - 1 : Nat) : Int) ≤ pl := by grind only
      omega

private theorem openssl_ca {c : AbstractCertificate} (hc : OpenSSL.checkCa c = 1) :
    c.extBasicConstraints.any (·.isCA) = true ∧
    (match c.extKeyUsage with | some ku => ku.keyCertSign = true | none => True) := by
  cases hb : c.extBasicConstraints with
  | none =>
    simp only [OpenSSL.checkCa, hb, Option.any_none, Bool.false_eq_true, ↓reduceIte] at hc
    split at hc
    · contradiction
    · split at hc <;> contradiction
  | some bc =>
    cases hk : c.extKeyUsage with
    | none =>
      cases hbc : bc.isCA <;>
        simp [OpenSSL.checkCa, hb, hk, hbc] at hc ⊢
    | some ku =>
      cases hbc : bc.isCA <;> cases hku : ku.keyCertSign <;>
        simp [OpenSSL.checkCa, hb, hk, hbc, hku] at hc ⊢

private theorem openssl_inter_ca {task c d}
    (hc : Verdict.opensslValidIntermediate task c d = true) : OpenSSL.checkCa c = 1 := by
  simp only [Verdict.opensslValidIntermediate, OpenSSL.validCertCommon, Bool.and_eq_true,
    Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hc
  grind only

private theorem openssl_root_ca {task c d}
    (hc : Verdict.opensslValidRoot task c d = true) : OpenSSL.checkCa c = 1 := by
  simp only [Verdict.opensslValidRoot, OpenSSL.validCertCommon, Bool.and_eq_true,
    Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hc
  grind only

theorem openssl_basic_constraints_ca :
  BasicConstraintsCA Verdict.opensslValidChain := by
  intro chain task h
  apply openssl_nonleaf (fun c => c.extBasicConstraints.any (·.isCA) = true) h
  · intro c d hc; exact (openssl_ca (openssl_inter_ca hc)).1
  · intro c d hc; exact (openssl_ca (openssl_root_ca hc)).1

theorem openssl_key_usage_ca :
  KeyUsageCA Verdict.opensslValidChain := by
  intro chain task h
  apply openssl_nonleaf (fun c => match c.extKeyUsage with
    | some ku => ku.keyCertSign = true | none => True) h
  · intro c d hc; exact (openssl_ca (openssl_inter_ca hc)).2
  · intro c d hc; exact (openssl_ca (openssl_root_ca hc)).2

theorem openssl_key_usage_leaf :
  KeyUsageLeaf Verdict.opensslValidChain := by
  intro chain task h _
  have hc := (openssl_parts h).2.1
  generalize he : chain[0]! = c at hc ⊢
  cases hk : c.extKeyUsage <;>
    simp [Verdict.opensslValidLeaf, OpenSSL.validCertCommon, OpenSSL.checkPurpose, hk,
      Bool.and_eq_true] at hc ⊢
  grind only

theorem chrome_subject_alt_name_present :
  ∀ (env : Verdict.Policy.ChromePolicyEnv),
    SubjectAltNamePresent (Verdict.chromeValidChain env) := by
  intro env chain task h _ hh
  have hc := (chrome_parts h).2.1
  generalize he : chain[0]! = c at hc ⊢
  cases ht : task.hostname with
  | none => simp [ht] at hh
  | some host =>
    cases hs : c.extSubjectAltName <;>
      simp [Verdict.chromeCertVerifiedLeaf, Chrome.Reference.matchSanDomain, ht, hs,
        Bool.and_eq_true] at hc ⊢

theorem chrome_sig_alg_consistency :
  ∀ env, SigAlgConsistency (Verdict.chromeValidChain env) := by
  intro env chain task h
  apply chrome_all (fun c => c.sigAlgOuter.bytes = c.sigAlgInner.bytes) h
  · intro c r hc
    simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true, beq_iff_eq] at hc
    grind only
  · intro c d hc
    simp only [Verdict.chromeCertVerifiedIntermediate, Chrome.Reference.certVerifiedNonLeaf,
      Bool.and_eq_true, beq_iff_eq] at hc
    grind only
  · intro c r d hc
    simp only [Verdict.chromeCertVerifiedRoot, Chrome.Reference.certVerifiedNonLeaf,
      Bool.and_eq_true, beq_iff_eq] at hc
    grind only

theorem firefox_sig_alg_consistency :
  ∀ env, SigAlgConsistency (Verdict.firefoxValidChain env) := by
  intro env chain task h
  apply firefox_all (fun c => c.sigAlgOuter.bytes = c.sigAlgInner.bytes) h
  · intro c hc
    simp only [Verdict.firefoxCertVerifiedLeaf, Bool.and_eq_true, beq_iff_eq] at hc
    grind only
  · intro c l d hc
    simp only [Verdict.firefoxCertVerifiedIntermediate, Firefox.Reference.nonLeaf,
      Bool.and_eq_true, beq_iff_eq] at hc
    grind only
  · intro c r l d hc
    simp only [Verdict.firefoxCertVerifiedRoot, Firefox.Reference.nonLeaf,
      Bool.and_eq_true, beq_iff_eq] at hc
    grind only

theorem openssl_sig_alg_consistency : SigAlgConsistency Verdict.opensslValidChain := by
  intro chain task h
  apply openssl_all (fun c => c.sigAlgOuter.bytes = c.sigAlgInner.bytes) h <;> intros <;>
    simp_all only [Verdict.opensslValidLeaf, Verdict.opensslValidIntermediate,
      Verdict.opensslValidRoot, OpenSSL.validCertCommon, Bool.and_eq_true, beq_iff_eq] <;>
    grind only

theorem chrome_strong_signature :
  ∀ env, StrongSignature (Verdict.chromeValidChain env) Chrome.strongSignature := by
  intro env chain task h i hi
  by_cases hz : i = 0
  · subst i
    have hc := (chrome_parts h).2.1
    simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true] at hc
    grind only
  · have hc := chrome_middle h (by omega : 0 < i) hi
    simp only [Verdict.chromeCertVerifiedIntermediate, Bool.and_eq_true] at hc
    grind only

private theorem firefox_strong_inner {alg : String}
    (h : Firefox.Reference.strongSignature alg = true) : Firefox.strongSignature alg = true := by
  simp [Firefox.Reference.strongSignature] at h
  simp [Firefox.strongSignature, Chrome.strongSignature]
  grind only

theorem firefox_strong_signature :
  ∀ env, StrongSignature (Verdict.firefoxValidChain env) Firefox.strongSignature := by
  intro env chain task h i hi
  apply firefox_strong_inner
  by_cases hz : i = 0
  · subst i
    have hc := (firefox_parts h).2.1
    simp only [List.getD_eq_getElem?_getD, ← List.getElem!_eq_getElem?_getD] at hc
    simp only [Verdict.firefoxCertVerifiedLeaf, Bool.and_eq_true] at hc
    grind only
  · have hc := firefox_middle h (by omega : 0 < i) hi
    simp only [Verdict.firefoxCertVerifiedIntermediate, Bool.and_eq_true] at hc
    grind only

theorem chrome_key_usage_leaf :
  ∀ (env : ChromePolicyEnv) chain task,
    Verdict.chromeValidChain env chain task = true → chain.length ≥ 1 →
    match chain[0]!.extKeyUsage with
    | some ku => if chain[0]!.extBasicConstraints.any (·.isCA) then ku.keyCertSign = true
                 else (ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement) = true
    | none => True := by
  intro env chain task h _
  have hc := (chrome_parts h).2.1
  generalize he : chain[0]! = c at hc ⊢
  have hk : Chrome.keyUsageValid c = true := by
    simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true] at hc
    grind only
  cases hu : c.extKeyUsage with
  | none => simp [hu]
  | some ku =>
    cases hb : c.extBasicConstraints with
    | none => simp [Chrome.keyUsageValid, hu, hb, Bool.and_eq_true] at hk ⊢; grind only
    | some bc =>
      cases hi : bc.isCA <;>
        simp [Chrome.keyUsageValid, hu, hb, hi, Bool.and_eq_true] at hk ⊢ <;>
        grind only

theorem chrome_extended_key_usage_leaf :
  ∀ (env : ChromePolicyEnv) chain task,
    Verdict.chromeValidChain env chain task = true → chain.length ≥ 1 →
    match chain[0]!.extExtendedKeyUsage with
    | some eku => eku.usages.any (fun u => u == .serverAuth || u == .any) = true
    | none => True := by
  intro env chain task h _
  have hc := (chrome_parts h).2.1
  generalize he : chain[0]! = c at hc ⊢
  have hk : Chrome.extendedKeyUsageValid c = true := by
    simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true] at hc
    grind only
  have heq : (fun u : ExtendedKeyUsageType => match u with
      | .serverAuth => true | .any => true | _ => false) =
      (fun u => u == .serverAuth || u == .any) := by
    funext u; cases u <;> rfl
  cases hu : c.extExtendedKeyUsage with
  | none => simp [hu]
  | some eku =>
    simp only [Chrome.extendedKeyUsageValid, hu] at hk
    rw [← heq]
    exact hk

theorem chrome_not_revoked :
  ∀ (env : ChromePolicyEnv) chain task,
    Verdict.chromeValidChain env chain task = true →
    ∀ i, i + 1 < chain.length → Chrome.notInCrl env chain[i]! = true := by
  intro env chain task h i hi
  by_cases hz : i = 0
  · subst i
    have hc := (chrome_parts h).2.1
    simp only [Verdict.chromeCertVerifiedLeaf, Bool.and_eq_true] at hc
    grind only
  · have hc := chrome_middle h (by omega : 0 < i) hi
    simp only [Verdict.chromeCertVerifiedIntermediate, Bool.and_eq_true] at hc
    grind only

theorem chrome_authority_key_id_valid :
  ∀ env, AuthorityKeyIdValid (Verdict.chromeValidChain env) := by
  intro env chain task h i hi
  simp only [Verdict.chromeValidChain, Bool.and_eq_true] at h
  have ha := h.2.2
  exact List.all_eq_true.mp ha i (List.mem_range.mpr (by omega))

theorem firefox_authority_key_id_valid :
  ∀ (env : FirefoxPolicyEnv) chain task,
    (∀ i, i + 1 < chain.length → Verdict.firefoxLikelyIssued chain[i + 1]! chain[i]! = true) →
    Verdict.firefoxValidChain env chain task = true →
    ∀ i, i + 1 < chain.length → checkAuthKeyId chain[i + 1]! chain[i]! = true := by
  intro env chain task hi _ i hn
  have hh := hi i hn
  change (_ && _) = true at hh
  simp only [Bool.and_eq_true] at hh
  exact hh.2

theorem openssl_authority_key_id_valid :
  ∀ chain task,
    (∀ i, i + 1 < chain.length → Verdict.opensslLikelyIssued chain[i + 1]! chain[i]! = true) →
    Verdict.opensslValidChain chain task = true →
    ∀ i, i + 1 < chain.length → checkAuthKeyId chain[i + 1]! chain[i]! = true := by
  intro chain task hi _ i hn
  have hh := hi i hn
  change (_ && _) = true at hh
  simp only [Bool.and_eq_true] at hh
  exact hh.2

theorem firefox_subject_alt_name_present :
  ∀ (env : FirefoxPolicyEnv) chain task,
    Verdict.firefoxValidChain env chain task = true → chain.length ≥ 1 →
    ∀ host, task.hostname = some host →
      chain[0]!.extSubjectAltName.isSome = true ∨
      (chain[0]!.extSubjectAltName = none ∧ Firefox.Reference.hostnameMatches chain[0]! host = true) := by
  intro env chain task h _ host ht
  have hc := (firefox_parts h).2.1
  simp only [List.getD_eq_getElem?_getD, ← List.getElem!_eq_getElem?_getD] at hc
  have hh : Firefox.Reference.hostnameMatches chain[0]! host = true := by
    simp only [Verdict.firefoxCertVerifiedLeaf, ht, Bool.and_eq_true] at hc
    grind only
  cases hs : chain[0]!.extSubjectAltName
  · exact Or.inr ⟨rfl, hh⟩
  · exact Or.inl (by simp [hs])

theorem openssl_subject_alt_name_present :
  ∀ chain task,
    Verdict.opensslValidChain chain task = true → chain.length ≥ 1 →
    ∀ host, task.hostname = some host →
      chain[0]!.extSubjectAltName.isSome = true ∨
      (chain[0]!.extSubjectAltName = none ∧ Verdict.opensslCheckHostname chain[0]! host = true) := by
  intro chain task h _ host ht
  have hh : Verdict.opensslCheckHostname chain[0]! host = true := by
    simpa only [ht] using (openssl_parts h).2.2.2.2.2
  cases hs : chain[0]!.extSubjectAltName
  · exact Or.inr ⟨rfl, hh⟩
  · exact Or.inl (by simp [hs])

private theorem firefox_version_guard {c : AbstractCertificate}
    (h : Firefox.Reference.checkExtensionVersion c = true) :
    c.allExts.isSome = true → c.version = 2 := by
  cases he : c.allExts <;> simp [Firefox.Reference.checkExtensionVersion, he] at h ⊢
  exact h

private theorem openssl_version_guard {c : AbstractCertificate}
    (h : OpenSSL.checkExtensionVersion c = true) :
    c.allExts.isSome = true → c.version = 2 := by
  cases he : c.allExts <;> simp [OpenSSL.checkExtensionVersion, he] at h ⊢
  exact h

theorem firefox_valid_version : ∀ env, ValidVersion (Verdict.firefoxValidChain env) := by
  intro env chain task h
  apply firefox_all (fun c => c.allExts.isSome = true → c.version = 2) h
  · intro c hc
    apply firefox_version_guard
    simp only [Verdict.firefoxCertVerifiedLeaf, Bool.and_eq_true] at hc
    grind only
  · intro c l d hc
    apply firefox_version_guard
    simp only [Verdict.firefoxCertVerifiedIntermediate, Bool.and_eq_true] at hc
    grind only
  · intro c r l d hc
    apply firefox_version_guard
    simp only [Verdict.firefoxCertVerifiedRoot, Bool.and_eq_true] at hc
    grind only

theorem openssl_valid_version : ValidVersion Verdict.opensslValidChain := by
  intro chain task h
  apply openssl_all (fun c => c.allExts.isSome = true → c.version = 2) h
  · intro c hc
    apply openssl_version_guard
    change (_ && _) = true at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · intro c d hc
    apply openssl_version_guard
    change (_ && _) = true at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · intro c d hc
    apply openssl_version_guard
    change (_ && _) = true at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2

namespace Historical

/- Historical counterexamples concern these executable pre-amendment policies and old
   predicates only. They are not certificates about the revised canonical instance. -/
private def oldSigAlgConsistency (validChain : List AbstractCertificate → PolicyTask → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i < chain.length → chain[i]!.sigAlgOuter.id = chain[i]!.sigAlgInner.id
private def oldStrongSignature (validChain : List AbstractCertificate → PolicyTask → Bool)
    (isStrong : String → Bool) : Prop :=
  ∀ chain task, validChain chain task = true →
    ∀ i, i + 1 < chain.length → isStrong chain[i]!.sigAlgOuter.id = true

open Verdict.Policy.Firefox.Reference Verdict.Policy.Firefox in
private def oldFirefoxNonLeaf (env : FirefoxPolicyEnv) (task : PolicyTask)
    (cert leaf : AbstractCertificate) (depth : Nat) : Bool :=
  internationalValid env cert leaf && validPki cert && depth ≤ 6 &&
  (match cert.extBasicConstraints with
    | none => false
    | some bc => bc.isCA && (match bc.pathLen with
      | none => true
      | some limit => limit ≥ 0 && (depth : Int) ≤ limit)) &&
  cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
  cert.notBefore ≤ task.now && task.now ≤ cert.notAfter &&
  checkKeyUsageIntermediate cert &&
  (match cert.extAuthorityKeyId with
    | none => true
    | some aki => aki.critical != some true) &&
  !cert.subject.rdns.isEmpty && checkDuplicateExtensions cert &&
  handledExtensions cert && subjectKeyIdNoncritical cert

open Verdict.Policy.OpenSSL in
private def oldOpenSSLCommon (task : PolicyTask) (cert : AbstractCertificate)
    (isLeaf isRoot : Bool) (depth : Nat) : Bool :=
  checkCertKeyLevel cert && checkCertTime cert task.now &&
  checkBasicConstraints cert && checkKeyUsage cert &&
  (if isLeaf then checkCa cert != 2 else checkCa cert == 1) &&
  !cert.issuer.rdns.isEmpty &&
  (!cert.subject.rdns.isEmpty ||
    (cert.extSubjectAltName.any (fun san => !san.names.isEmpty && san.critical == some true) &&
     !cert.extBasicConstraints.any (fun bc => bc.isCA) &&
     !cert.extKeyUsage.any (fun ku => ku.keyCertSign))) &&
  checkSan cert && cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
  checkPurpose cert isLeaf && checkAuthSubjectKeyId cert isRoot isLeaf &&
  (match cert.extBasicConstraints with
   | none => true
   | some bc => match bc.pathLen with
     | none => true
     | some pathLen => pathLen >= 0 && (isLeaf || (depth : Int) <= pathLen)) &&
  checkUnhandledExtensions cert && checkDuplicateExts cert

private def oldFirefoxLeaf : Verdict.FirefoxCertVerifiedLeafSig :=
  fun env task cert ev =>
    Verdict.Policy.Firefox.Reference.validPki cert &&
    (match task.hostname with
      | none => true
      | some domain => Verdict.Policy.Firefox.Reference.hostnameMatches cert domain) &&
    (match cert.extBasicConstraints with
      | none => true
      | some bc => !bc.isCA) &&
    (!ev || (cert.notBefore ≤ cert.notAfter && cert.notAfter - cert.notBefore < 71712000)) &&
    !env.crl.contains cert.fingerprint &&
    cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
    cert.notBefore ≤ task.now && task.now ≤ cert.notAfter &&
    Verdict.Policy.Firefox.Reference.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Firefox.checkKeyUsageLeaf cert &&
    Verdict.Policy.Firefox.Reference.extendedKeyUsage cert &&
    Verdict.Policy.checkDuplicateExtensions cert &&
    Verdict.Policy.Firefox.Reference.handledExtensions cert &&
    Verdict.Policy.Firefox.Reference.subjectKeyIdNoncritical cert

private def oldFirefoxIntermediate : Verdict.FirefoxCertVerifiedIntermediateSig :=
  fun env task cert leaf depth =>
    oldFirefoxNonLeaf env task cert leaf depth &&
    !env.crl.contains cert.fingerprint &&
    Verdict.Policy.Firefox.Reference.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Firefox.Reference.extendedKeyUsage cert

private def oldFirefoxRoot : Verdict.FirefoxCertVerifiedRootSig :=
  fun env task cert interm leaf depth =>
    oldFirefoxNonLeaf env task cert leaf depth &&
    !(env.symantecRoots.contains cert.fingerprint &&
      !env.symantecExceptions.contains interm.fingerprint && cert.notBefore < 1464739200) &&
    Verdict.Policy.Firefox.Reference.internationalValid env cert leaf

private def oldOpenSSLLeaf : Verdict.OpensslValidLeafSig :=
  fun task cert => oldOpenSSLCommon task cert true false 0

private def oldOpenSSLIntermediate : Verdict.OpensslValidIntermediateSig :=
  fun task cert depth => oldOpenSSLCommon task cert false false depth

private def oldOpenSSLRoot : Verdict.OpensslValidRootSig :=
  fun task cert depth => oldOpenSSLCommon task cert false true depth

private def oldChromeValidChain : Verdict.ChromeValidChainSig :=
  fun env chain task =>
    chain.length ≥ 2 &&
    Verdict.chromeCertVerifiedLeaf env task chain[0]! chain[chain.length - 1]! &&
    (List.range (chain.length - 2)).all (fun depth =>
      Verdict.chromeCertVerifiedIntermediate env task chain[depth + 1]! depth) &&
    Verdict.chromeCertVerifiedRoot env task chain[chain.length - 1]!
      chain[chain.length - 2]! (chain.length - 2) &&
    Verdict.chromeCheckAllNameConstraints chain

private def oldFirefoxValidChain : Verdict.FirefoxValidChainSig :=
  fun env chain task =>
    chain.length ≥ 2 &&
    oldFirefoxLeaf env task (chain.getD 0 default) false &&
    ((List.range (chain.length - 2)).all fun depth =>
      oldFirefoxIntermediate env task (chain.getD (depth + 1) default)
        (chain.getD 0 default) depth) &&
    oldFirefoxRoot env task (chain.getD (chain.length - 1) default)
      (chain.getD (chain.length - 2) default) (chain.getD 0 default) (chain.length - 2) &&
    Verdict.firefoxCheckAllNameConstraints chain

private def oldOpenSSLValidChain : Verdict.OpensslValidChainSig :=
  fun chain task =>
    chain.length >= 2 &&
    oldOpenSSLLeaf task chain[0]! &&
    ((List.range (chain.length - 2)).all fun offset =>
      oldOpenSSLIntermediate task chain[offset + 1]! offset) &&
    oldOpenSSLRoot task chain[chain.length - 1]! (chain.length - 2) &&
    Verdict.opensslCheckNameConstraints chain &&
    (match task.hostname with
     | none => true
     | some hostname => Verdict.opensslCheckHostname chain[0]! hostname)

private def witnessTask : PolicyTask := { hostname := none, purpose := .serverAuth, now := 1 }
private def witnessLeaf : AbstractCertificate := {
  (default : AbstractCertificate) with
  fingerprint := "leaf"
  version := 2
  subjectKey := .other
  notBefore := 0
  notAfter := 2
  subject := { rdns := [[{ oid := "2.5.4.3", value := "a" }]] }
  issuer := { rdns := [[{ oid := "2.5.4.3", value := "issuer" }]] }
  sigAlgInner := { id := "1.2.840.113549.1.1.11", bytes := "" }
  sigAlgOuter := { id := "different", bytes := "" }
  extAuthorityKeyId := some { critical := none, keyId := some "wrong", issuer := none, serial := none }
}
private def witnessRoot : AbstractCertificate := {
  witnessLeaf with
  fingerprint := "root"
  extBasicConstraints := some { critical := some true, isCA := true, pathLen := none }
  extKeyUsage := some { (default : KeyUsage) with keyCertSign := true }
  extSubjectKeyId := some { critical := none, keyId := "root-key" }
}
private def coherentLeaf : AbstractCertificate := { witnessLeaf with sigAlgOuter := witnessLeaf.sigAlgInner }
private def coherentRoot : AbstractCertificate := {
  witnessRoot with sigAlgOuter := witnessRoot.sigAlgInner, subject := witnessLeaf.issuer }
private theorem chrome_coherent_witness : oldChromeValidChain default [coherentLeaf, coherentRoot] witnessTask = true := by decide
private theorem firefox_coherent_witness : oldFirefoxValidChain default [coherentLeaf, coherentRoot] witnessTask = true := by decide
private theorem openssl_coherent_witness : oldOpenSSLValidChain [coherentLeaf, coherentRoot] witnessTask = true := by decide

private theorem chrome_witness : oldChromeValidChain default [witnessLeaf, witnessRoot] witnessTask = true := by decide
private theorem firefox_witness : oldFirefoxValidChain default [witnessLeaf, witnessRoot] witnessTask = true := by decide
private theorem openssl_witness : oldOpenSSLValidChain [witnessLeaf, witnessRoot] witnessTask = true := by decide

theorem chrome_sig_alg_consistency_refuted :
  ¬ (∀ (env : Verdict.Policy.ChromePolicyEnv),
    oldSigAlgConsistency (oldChromeValidChain env)) := by
  intro h
  have hh := h default [witnessLeaf, witnessRoot] witnessTask chrome_witness 0 (by decide)
  exact (by decide : ¬ ("different" = "1.2.840.113549.1.1.11")) hh

theorem firefox_sig_alg_consistency_refuted :
  ¬ (∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    oldSigAlgConsistency (oldFirefoxValidChain env)) := by
  intro h
  have hh := h default [witnessLeaf, witnessRoot] witnessTask firefox_witness 0 (by decide)
  exact (by decide : ¬ ("different" = "1.2.840.113549.1.1.11")) hh

theorem openssl_sig_alg_consistency_refuted :
  ¬ (oldSigAlgConsistency oldOpenSSLValidChain) := by
  intro h
  have hh := h [witnessLeaf, witnessRoot] witnessTask openssl_witness 0 (by decide)
  exact (by decide : ¬ ("different" = "1.2.840.113549.1.1.11")) hh

theorem chrome_strong_signature_refuted :
  ¬ (∀ (env : Verdict.Policy.ChromePolicyEnv),
    oldStrongSignature (oldChromeValidChain env) Verdict.Policy.Chrome.strongSignature) := by
  intro h
  have hh := h default [witnessLeaf, witnessRoot] witnessTask chrome_witness 0 (by decide)
  change false = true at hh
  contradiction

theorem firefox_strong_signature_refuted :
  ¬ (∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    oldStrongSignature (oldFirefoxValidChain env) Verdict.Policy.Firefox.strongSignature) := by
  intro h
  have hh := h default [witnessLeaf, witnessRoot] witnessTask firefox_witness 0 (by decide)
  change false = true at hh
  contradiction

theorem chrome_authority_key_id_valid_refuted :
  ¬ (∀ (env : Verdict.Policy.ChromePolicyEnv),
    AuthorityKeyIdValid (oldChromeValidChain env)) := by
  intro h
  have hh := h default [coherentLeaf, coherentRoot] witnessTask chrome_coherent_witness 0 (by decide)
  change false = true at hh
  contradiction

theorem firefox_authority_key_id_valid_refuted :
  ¬ (∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    AuthorityKeyIdValid (oldFirefoxValidChain env)) := by
  intro h
  have hh := h default [coherentLeaf, coherentRoot] witnessTask firefox_coherent_witness 0 (by decide)
  change false = true at hh
  contradiction

theorem openssl_authority_key_id_valid_refuted :
  ¬ (AuthorityKeyIdValid oldOpenSSLValidChain) := by
  intro h
  have hh := h [coherentLeaf, coherentRoot] witnessTask openssl_coherent_witness 0 (by decide)
  change false = true at hh
  contradiction

private def witnessCALeaf : AbstractCertificate := {
  coherentLeaf with
  extBasicConstraints := some { critical := some true, isCA := true, pathLen := none }
  extKeyUsage := some { (default : KeyUsage) with keyCertSign := true }
}
theorem chrome_key_usage_leaf_refuted :
  ¬ (∀ (env : Verdict.Policy.ChromePolicyEnv),
    KeyUsageLeaf (oldChromeValidChain env)) := by
  intro h
  have hh := h default [witnessCALeaf, coherentRoot] witnessTask (by decide) (by decide)
  change false = true at hh
  contradiction

private def witnessAnyEKU : AbstractCertificate := {
  coherentLeaf with extExtendedKeyUsage := some { critical := none, usages := [.any] }
}
theorem chrome_extended_key_usage_leaf_refuted :
  ¬ (∀ (env : Verdict.Policy.ChromePolicyEnv),
    ExtendedKeyUsageLeaf (oldChromeValidChain env)) := by
  intro h
  have hh := h default [witnessAnyEKU, coherentRoot] witnessTask (by decide) (by decide)
  change false = true at hh
  contradiction

theorem chrome_not_revoked_refuted :
  ¬ (∀ (env : Verdict.Policy.ChromePolicyEnv),
    NotRevoked (oldChromeValidChain env) (Verdict.Policy.Chrome.notInCrl env)) := by
  intro h
  let env : ChromePolicyEnv := { (default : ChromePolicyEnv) with crl := ["root"] }
  have hh := h env [coherentLeaf, coherentRoot] witnessTask (by decide) 1 (by decide)
  change false = true at hh
  contradiction

private def witnessHostTask : PolicyTask := { witnessTask with hostname := some "a" }
private theorem host_not_wildcard : "a".startsWith "*." = false := by decide
private theorem host_not_leading_dot : "a".startsWith "." = false := by
  change String.Slice.Pattern.ForwardSliceSearcher.startsWith ".".toSlice "a".toSlice = false
  simp only [Bool.eq_false_iff, String.Slice.Pattern.ForwardSliceSearcher.startsWith]
  simp only [show (".".toSlice.utf8ByteSize ≤ "a".toSlice.utf8ByteSize) by decide, dite_true]
  simp only [ne_eq, String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff]
  decide
private theorem host_not_trailing_dot : "a".endsWith "." = false := by
  change String.Slice.Pattern.BackwardSliceSearcher.endsWith ".".toSlice "a".toSlice = false
  simp only [Bool.eq_false_iff, String.Slice.Pattern.BackwardSliceSearcher.endsWith]
  simp only [show (".".toSlice.utf8ByteSize ≤ "a".toSlice.utf8ByteSize) by decide, dite_true]
  simp only [ne_eq, String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff]
  decide
private theorem host_lower : Verdict.Policy.Reference.lowerString "a" = "a" := by decide
private theorem host_no_star : ("a".any (· == '*')) = false := by
  have hs : "a".toSlice.startPos ≠ "a".toSlice.endPos := by
    intro h
    have hh := congrArg (fun p => p.offset.byteIdx) h
    change (0 : Nat) = 1 at hh
    contradiction
  have hd : ∀ h, String.Slice.Pattern.ForwardPattern.dropPrefixOfNonempty? (fun c => c == '*')
      ("a".toSlice.sliceFrom "a".toSlice.startPos) h = none := by intro h; rfl
  simp only [String.any, String.contains, String.Slice.contains]
  rw [Std.Iter.any_eq_match_step, Std.Iter.step_eq]
  dsimp [String.Slice.Pattern.ToForwardSearcher.toSearcher,
    String.Slice.Pattern.ToForwardSearcher.defaultImplementation,
    String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.iter]
  simp only [hs, ↓reduceDIte]
  split <;> rename_i heq
  · split at heq <;> rename_i heq'
    · rw [hd (by decide)] at heq'
      contradiction
    · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
        Std.PlausibleIterStep.yield, Std.IterStep.yield.injEq] at heq
      rw [← heq.1, ← heq.2]
      dsimp
      rw [Std.Iter.any_eq_match_step, Std.Iter.step_eq]
      simp only [Std.Iter.toIterM]
      have hn : "a".toSlice.startPos.next hs = "a".toSlice.endPos := by
        apply String.Slice.Pos.ext
        apply String.Pos.Raw.ext
        rw [String.Slice.Pos.byteIdx_offset_next]
        rfl
      simp only [hn, ↓reduceDIte, Id.run_pure, Std.Shrink.inflate_deflate]
      rfl
  · split at heq <;> simp at heq
  · split at heq <;> simp at heq

private theorem firefox_host_matches : Firefox.Reference.hostnameMatches coherentLeaf "a" = true := by
  dsimp [Firefox.Reference.hostnameMatches, coherentLeaf, witnessLeaf]
  have hd : (default : AbstractCertificate).extSubjectAltName = none := by rfl
  simp [Firefox.Reference.validName, matchName, host_lower, host_not_wildcard,
    host_not_leading_dot, host_not_trailing_dot, host_no_star, hd, show "a".isEmpty = false by decide]
private theorem openssl_host_matches : Verdict.opensslCheckHostname coherentLeaf "a" = true := by
  dsimp [Verdict.opensslCheckHostname, coherentLeaf, witnessLeaf, OpenSSL.checkSanHasDns]
  have hd : (default : AbstractCertificate).extSubjectAltName = none := by rfl
  simp [OpenSSL.checkValidPattern, matchName, host_lower, host_not_wildcard, hd]
private theorem firefox_host_witness : oldFirefoxValidChain default [coherentLeaf, coherentRoot] witnessHostTask = true := by
  have hl : oldFirefoxLeaf default witnessHostTask coherentLeaf false = true := by
    simp only [oldFirefoxLeaf, witnessHostTask, witnessTask, firefox_host_matches]
    decide
  change (_ && oldFirefoxLeaf default witnessHostTask coherentLeaf false && _ && _ && _) = true
  rw [hl]
  decide

private theorem openssl_host_witness : oldOpenSSLValidChain [coherentLeaf, coherentRoot] witnessHostTask = true := by
  change (_ && _ && _ && _ && _ && Verdict.opensslCheckHostname coherentLeaf "a") = true
  rw [openssl_host_matches]
  decide

theorem firefox_subject_alt_name_present_refuted :
  ¬ (∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    SubjectAltNamePresent (oldFirefoxValidChain env)) := by
  intro h
  have hh := h default [coherentLeaf, coherentRoot] witnessHostTask firefox_host_witness (by decide) (by decide)
  change false = true at hh
  contradiction

theorem openssl_subject_alt_name_present_refuted :
  ¬ (SubjectAltNamePresent oldOpenSSLValidChain) := by
  intro h
  have hh := h [coherentLeaf, coherentRoot] witnessHostTask openssl_host_witness (by decide) (by decide)
  change false = true at hh
  contradiction

private def witnessVersion : AbstractCertificate := { coherentLeaf with version := 3, allExts := some [] }
theorem firefox_valid_version_refuted :
  ¬ (∀ (env : Verdict.Policy.FirefoxPolicyEnv),
    ValidVersion (oldFirefoxValidChain env)) := by
  intro h
  have hh := h default [witnessVersion, coherentRoot] witnessTask (by decide) 0 (by decide) (by decide)
  exact (by decide : ¬ ((3 : UInt32) = 2)) hh

theorem openssl_valid_version_refuted :
  ¬ (ValidVersion oldOpenSSLValidChain) := by
  intro h
  have hh := h [witnessVersion, coherentRoot] witnessTask (by decide) 0 (by decide) (by decide)
  exact (by decide : ¬ ((3 : UInt32) = 2)) hh

end Historical

end VerdictCertificates.Standard
