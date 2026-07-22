/*!
 * Curated alias lexicon for the (closed, small) causal-inference / econometrics
 * vocabulary. It exists to bridge the vocabulary-mismatch failure of pure keyword
 * retrieval: an F1 plan may say "ignorability" while the Causalean declaration is
 * named `ConditionalExchangeability` — zero shared tokens, so keyword match alone
 * never surfaces it. Each entry maps a canonical concept to its synonyms and to the
 * Causalean module/area prefixes where that concept's declarations live.
 *
 * Two consumers (see reuse_retrieval.ts):
 *   1. Query expansion — before scoring, a query's terms are widened with the
 *      synonyms of every matched concept, so "ignorability" also matches on
 *      "exchangeability" / "unconfoundedness".
 *   2. Module-level fallback — when no indexed declaration scores, the matched
 *      concepts' `modules` point the agent at the right area to search by hand.
 *
 * Maintenance: this is meant to GROW from friction logs. Every time a run
 * re-derives a Causalean declaration because the words differed, add the missing
 * synonym here. Keep it high-precision (genuine synonyms only) — a loose alias
 * floods every query with false candidates.
 */

export interface AliasEntry {
  /** Canonical concept label (human-facing; also a surface form for matching). */
  canonical: string;
  /** Synonyms / alternate phrasings that denote the same concept. */
  aliases: string[];
  /** Causalean file/module path prefixes where this concept's decls live. */
  modules: string[];
}

/** Normalize a surface form / query fragment for matching: lowercase, `_`/`-`→space, collapse ws. */
export function normalizeConcept(s: string): string {
  return s.toLowerCase().replace(/[_\-]+/g, " ").replace(/\s+/g, " ").trim();
}

export const CAUSAL_ALIASES: AliasEntry[] = [
  {
    canonical: "aipw",
    aliases: ["augmented inverse probability weighted estimator","augmented inverse probability weighting","augmented ipw"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Estimation/Efficiency/"],
  },
  {
    canonical: "asymptotic normality",
    aliases: ["asymptotically normal","central limit theorem","limit law","limiting distribution"],
    modules: ["Causalean/Stat/","Causalean/Stat/CLT/"],
  },
  {
    canonical: "augmented inverse probability weighting",
    aliases: ["aipw","double robustness","doubly robust","doubly robust estimator"],
    modules: ["Causalean/Estimation/","Causalean/Estimation/StructureAgnostic/"],
  },
  {
    canonical: "average treatment effect",
    aliases: ["ace","ate","average causal effect","mean treatment effect"],
    modules: ["Causalean/Estimation/ATE/","Causalean/PO/ID/Exact/ATE","Causalean/PO/ID/Exact/Frontdoor"],
  },
  {
    canonical: "average treatment effect on the treated",
    aliases: ["atet","att","average treatment effect among the treated","treatment effect on the treated"],
    modules: ["Causalean/Estimation/ATT/","Causalean/PO/ID/Exact/","Causalean/PO/ID/Exact/ATT"],
  },
  {
    canonical: "backdoor adjustment",
    aliases: ["adjustment formula","back door","back door adjustment","backdoor","backdoor formula","confounder adjustment","covariate adjustment","g formula","standardization"],
    modules: ["Causalean/PO/ID/Exact/","Causalean/PO/ID/Exact/ATE","Causalean/SCM/","Causalean/SCM/ID/Adjustment","Causalean/SCM/ID/Backdoor","Causalean/SCM/ID/BackdoorCriterion"],
  },
  {
    canonical: "balke pearl bounds",
    aliases: ["bp bounds"],
    modules: ["Causalean/PO/ID/Partial/BalkePearl/"],
  },
  {
    canonical: "bayes ball",
    aliases: ["bayes ball algorithm"],
    modules: ["Causalean/Graph/DSep/"],
  },
  {
    canonical: "bootstrap",
    aliases: ["bootstrap resampling","nonparametric bootstrap","resampling bootstrap"],
    modules: ["Causalean/Stat/Inference/"],
  },
  {
    canonical: "borusyak jaravel spiess",
    aliases: ["bjs","bjs imputation","borusyak imputation","borusyak jaravel spiess imputation"],
    modules: ["Causalean/Panel/EstimandCharacterization/ImputationEventStudy/"],
  },
  {
    canonical: "bracketing entropy",
    aliases: ["bracketing covering number","bracketing number","bracketing numbers","l1 bracketing number"],
    modules: ["Causalean/Stat/EmpiricalProcess/"],
  },
  {
    canonical: "c component",
    aliases: ["bidirected component","confounded component","district"],
    modules: ["Causalean/Graph/","Causalean/SCM/ID/"],
  },
  {
    canonical: "callaway sant'anna",
    aliases: ["callaway and sant'anna","callaway santanna","callaway santanna did","cs did","csdid"],
    modules: ["Causalean/PO/ID/Exact/CSDID.lean"],
  },
  {
    canonical: "cate meta learner",
    aliases: ["cate metalearner","conditional average treatment effect meta learner","conditional average treatment effect metalearner","heterogeneous treatment effect meta learner","heterogeneous treatment effect metalearner"],
    modules: ["Causalean/Estimation/CATE/"],
  },
  {
    canonical: "central limit theorem",
    aliases: ["asymptotic gaussianity","asymptotic normality","clt","convergence to a normal law","normal limit"],
    modules: ["Causalean/Estimation/","Causalean/Stat/CLT/","Causalean/Stat/Inference/"],
  },
  {
    canonical: "collider",
    aliases: ["collider node","collider triple","colliding node"],
    modules: ["Causalean/Graph/DSep/"],
  },
  {
    canonical: "concentration inequality",
    aliases: ["concentration bound","deviation inequality","exponential inequality","tail bound"],
    modules: ["Causalean/Stat/Concentration/"],
  },
  {
    canonical: "conditional average treatment effect",
    aliases: ["cate","conditional average causal effect","conditional treatment effect","heterogeneous treatment effect"],
    modules: ["Causalean/Estimation/CATE/","Causalean/PO/ID/Exact/","Causalean/PO/ID/Exact/ATE"],
  },
  {
    canonical: "conditional exchangeability",
    aliases: ["conditional ignorability","conditional unconfoundedness","ignorability","no unmeasured confounding","selection on observables","unconfoundedness"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/CATE/","Causalean/PO/ID/Exact/"],
  },
  {
    canonical: "conditional independence",
    aliases: ["condindepfun","conditional independence of","conditionally independent","independence given"],
    modules: ["Causalean/Graph/","Causalean/PO/","Causalean/SCM/"],
  },
  {
    canonical: "confounder",
    aliases: ["common cause","common cause confounder","confounding variable"],
    modules: ["Causalean/Graph/","Causalean/PO/ID/Exact/","Causalean/SCM/Examples/"],
  },
  {
    canonical: "consistency",
    aliases: ["counterfactual consistency","factual consistency","no interference","observed outcome equals potential outcome","potential outcome consistency","stable unit treatment value","sutva"],
    modules: ["Causalean/Estimation/","Causalean/PO/","Causalean/PO/Conditioning/","Causalean/PO/ID/Exact/"],
  },
  {
    canonical: "control function",
    aliases: ["control function approach","control function method"],
    modules: ["Causalean/Estimation/NPIV/","Causalean/SCM/Examples/"],
  },
  {
    canonical: "counterfactual",
    aliases: ["counterfactual outcome","counterfactual variable","potential outcome","potential response"],
    modules: ["Causalean/PO/Core/","Causalean/PO/ID/","Causalean/SCM/Model/"],
  },
  {
    canonical: "covariate balancing",
    aliases: ["balancing weights","covariate balance","covariate balanced weighting"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Stat/PolynomialTail/"],
  },
  {
    canonical: "cross fitting",
    aliases: ["cross fit","cross fitted estimation"],
    modules: ["Causalean/Estimation/OrthogonalMoments/","Causalean/Stat/EmpiricalProcess/"],
  },
  {
    canonical: "d separation",
    aliases: ["bayes ball","blocked path","d sep","d separated","directed separation","dsep","graphical independence"],
    modules: ["Causalean/Graph/","Causalean/Graph/DSep/","Causalean/SCM/Do/"],
  },
  {
    canonical: "de chaisemartin d'haultfoeuille",
    aliases: ["dcdh","de chaisemartin and d'haultfoeuille","de chaisemartin dhaultfoeuille"],
    modules: ["Causalean/Panel/EstimandCharacterization/HeterogeneousTWFE/"],
  },
  {
    canonical: "delta method",
    aliases: ["directional delta method","functional delta method"],
    modules: ["Causalean/Stat/Inference/"],
  },
  {
    canonical: "difference in differences",
    aliases: ["common trends","did","did estimator","diff in diff","difference in difference","parallel trends","twfe","two way fixed effects"],
    modules: ["Causalean/PO/ID/Exact/CSDID.lean","Causalean/PO/ID/Exact/DID","Causalean/PO/ID/Exact/DID.lean","Causalean/Panel/","Causalean/Panel/EstimandCharacterization/"],
  },
  {
    canonical: "do calculus",
    aliases: ["do operator","intervention distribution","interventional distribution","pearl's do calculus","rules of do calculus"],
    modules: ["Causalean/SCM/Do/"],
  },
  {
    canonical: "double machine learning",
    aliases: ["cross fitting","debiased machine learning","debiased ml","dml","neyman orthogonality","orthogonal machine learning","orthogonal moment","orthogonal score","sample splitting"],
    modules: ["Causalean/Estimation/","Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Estimation/DTR/","Causalean/Estimation/OrthogonalMoments/","Causalean/Stat/Orthogonality/"],
  },
  {
    canonical: "doubly robust estimator",
    aliases: ["doubly robust estimation","doubly robust moment","doubly robust score","dr estimator"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Estimation/CATE/","Causalean/Estimation/NPIV/DR/"],
  },
  {
    canonical: "dr learner",
    aliases: ["doubly robust learner"],
    modules: ["Causalean/Estimation/CATE/","Causalean/Estimation/CATE/OSL/"],
  },
  {
    canonical: "dudley entropy integral",
    aliases: ["dudley integral","entropy integral","metric entropy integral"],
    modules: ["Causalean/Stat/EmpiricalProcess/"],
  },
  {
    canonical: "dynamic treatment effects",
    aliases: ["dynamic effects","dynamic treatment effect","event time treatment effects"],
    modules: ["Causalean/Panel/EstimandCharacterization/ImputationEventStudy/","Causalean/Panel/EstimandCharacterization/EventStudyContamination/"],
  },
  {
    canonical: "dynamic treatment regime",
    aliases: ["adaptive treatment strategy","dtr","dynamic treatment regimes","dynamic treatment rule","g methods","treatment regime"],
    modules: ["Causalean/Estimation/DTR/","Causalean/PO/ID/Exact/DTR/"],
  },
  {
    canonical: "e value",
    aliases: ["evalue"],
    modules: ["Causalean/Estimation/StructureAgnostic/","Causalean/PO/ID/Partial/SupportFunction/"],
  },
  {
    canonical: "efficiency bound",
    aliases: ["asymptotic variance","cramer rao","cramer rao bound","cramér rao bound","efficient influence function","hahn bound","influence function","information bound","semiparametric efficiency","semiparametric efficiency bound"],
    modules: ["Causalean/Estimation/Efficiency/","Causalean/Stat/","Causalean/Stat/GMM/"],
  },
  {
    canonical: "efficient influence function",
    aliases: ["canonical gradient","efficient influence curve","efficient influence score","eif"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/Efficiency/"],
  },
  {
    canonical: "empirical process",
    aliases: ["empirical process theory","uniform empirical process"],
    modules: ["Causalean/Stat/EmpiricalProcess/"],
  },
  {
    canonical: "event study",
    aliases: ["event study design","event time design","event time study"],
    modules: ["Causalean/Panel/EstimandCharacterization/ImputationEventStudy/","Causalean/Panel/EstimandCharacterization/EventStudyContamination/"],
  },
  {
    canonical: "exclusion restriction",
    aliases: ["exclusion assumption","exclusion restriction assumption","iv exclusion"],
    modules: ["Causalean/PO/ID/Exact/DynamicLATE/","Causalean/PO/ID/Exact/LATE","Causalean/PO/ID/Partial/BalkePearl/"],
  },
  {
    canonical: "faithfulness",
    aliases: ["causal faithfulness","faithful distribution","markov faithfulness"],
    modules: ["Causalean/Graph/DSep/","Causalean/SCM/Do/"],
  },
  {
    canonical: "fixed effects estimator",
    aliases: ["fe estimator","within estimator","within transformation"],
    modules: ["Causalean/Panel/FWLInstanceL2.lean","Causalean/Panel/FixedEffect.lean","Causalean/Panel/FixedEffect/","Causalean/Panel/Weighted/FWL.lean"],
  },
  {
    canonical: "frontdoor adjustment",
    aliases: ["front door","frontdoor","mediation formula"],
    modules: ["Causalean/PO/ID/Exact/Frontdoor"],
  },
  {
    canonical: "frontdoor formula",
    aliases: ["front door adjustment","front door criterion","front door formula","frontdoor adjustment","frontdoor criterion"],
    modules: ["Causalean/PO/ID/Exact/Frontdoor"],
  },
  {
    canonical: "g formula",
    aliases: ["g computation","g computation formula","standardization"],
    modules: ["Causalean/PO/ID/Exact/DTR/","Causalean/SCM/ID/GraphicalThms/DoGFormula","Causalean/SCM/ID/GraphicalThms/DoGFormulaTian"],
  },
  {
    canonical: "generalized method of moments",
    aliases: ["generalised method of moments","gmm","gmm estimation","gmm estimator"],
    modules: ["Causalean/Stat/GMM/","Causalean/Stat/MEstimation/"],
  },
  {
    canonical: "global markov property",
    aliases: ["causal markov property","global markov","markov property"],
    modules: ["Causalean/SCM/Do/","Causalean/SCM/ID/GraphicalThms/"],
  },
  {
    canonical: "graphical identifiability",
    aliases: ["causal identifiability","identifiability","nonparametric identifiability"],
    modules: ["Causalean/PO/ID/","Causalean/SCM/ID/"],
  },
  {
    canonical: "group time att",
    aliases: ["att(g,t)","cohort time att","group time average treatment effect on the treated","gt att"],
    modules: ["Causalean/PO/ID/Exact/CSDID.lean","Causalean/Panel/EstimandCharacterization/EventStudyContamination/","Causalean/Panel/EstimandCharacterization/FlexibleDIDMundlak/"],
  },
  {
    canonical: "id algorithm",
    aliases: ["identification algorithm","pearl id algorithm","shpitser pearl id algorithm"],
    modules: ["Causalean/SCM/ID/","Causalean/SCM/ID/GraphicalThms/"],
  },
  {
    canonical: "identified set",
    aliases: ["identification region","identified region","set identification","set identified"],
    modules: ["Causalean/PO/ID/Partial/","Causalean/PO/ID/Partial/SupportFunction/"],
  },
  {
    canonical: "ignorability",
    aliases: ["conditional exchangeability","conditional ignorability","conditional independence of potential outcomes","exchangeability","no unmeasured confounding","selection on observables","strong ignorability","unconfoundedness"],
    modules: ["Causalean/PO/ID/"],
  },
  {
    canonical: "influence function",
    aliases: ["asymptotic linear representation","asymptotic linearity","asymptotically linear","influence curve","influence function expansion"],
    modules: ["Causalean/Estimation/","Causalean/Estimation/Efficiency/","Causalean/Stat/GMM/","Causalean/Stat/MEstimation/"],
  },
  {
    canonical: "instrument",
    aliases: ["instrument variable","instrumental variable","iv"],
    modules: ["Causalean/Estimation/NPIV/","Causalean/PO/ID/Exact/","Causalean/SCM/Examples/"],
  },
  {
    canonical: "instrument relevance",
    aliases: ["first stage relevance","relevance","relevance assumption"],
    modules: ["Causalean/PO/ID/Exact/VariableIntensityIV/","Causalean/PO/ID/Exact/DynamicLATE/","Causalean/PO/ID/Exact/LATE"],
  },
  {
    canonical: "instrumental variable",
    aliases: ["exclusion restriction","instrument","instrument exogeneity","instrument relevance","instrumental variables","iv"],
    modules: ["Causalean/Estimation/NPIV/","Causalean/PO/ID/Exact/VariableIntensityIV/","Causalean/PO/ID/Exact/LATE","Causalean/SCM/","Causalean/SCM/Examples/"],
  },
  {
    canonical: "intention to treat effect",
    aliases: ["intent to treat effect","itt"],
    modules: ["Causalean/PO/ID/Exact/DynamicLATE/","Causalean/PO/ID/Exact/LATE"],
  },
  {
    canonical: "intersection bounds",
    aliases: ["intersection bound"],
    modules: ["Causalean/PO/ID/Partial/SupportFunction/"],
  },
  {
    canonical: "intervention",
    aliases: ["atomic intervention","do intervention","do operation","do operator"],
    modules: ["Causalean/SCM/Do/","Causalean/SCM/Model/"],
  },
  {
    canonical: "interventional distribution",
    aliases: ["do distribution","do law","interventional law","post intervention distribution"],
    modules: ["Causalean/SCM/Do/","Causalean/SCM/ID/"],
  },
  {
    canonical: "inverse probability weighting",
    aliases: ["horvitz thompson","horvitz thompson estimator","ht estimator","inverse probability weighted estimator","inverse propensity weighting","ipw","stabilized weights"],
    modules: ["Causalean/Estimation/","Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Estimation/DTR/"],
  },
  {
    canonical: "lee bounds",
    aliases: ["lee trimming bounds","trimming bounds"],
    modules: ["Causalean/PO/ID/Partial/Lee/"],
  },
  {
    canonical: "local average treatment effect",
    aliases: ["cace","complier","complier average causal effect","complier average treatment effect","compliers","late","wald estimand","wald ratio"],
    modules: ["Causalean/PO/ID/Exact/VariableIntensityIV/","Causalean/PO/ID/Exact/DynamicLATE/","Causalean/PO/ID/Exact/LATE","Causalean/PO/ID/Exact/RDD/"],
  },
  {
    canonical: "local markov property",
    aliases: ["local causal markov property","local markov"],
    modules: ["Causalean/SCM/Do/"],
  },
  {
    canonical: "local projections",
    // NB: no bare "lp" alias — it collides with Lebesgue `Lp`-space identifiers
    // (`aipwLp`, `imLp`, `reLp`), which are unrelated to Jordà local projections.
    aliases: ["jorda local projections","jordà local projections","local projection"],
    modules: ["Causalean/Estimation/"],
  },
  {
    canonical: "m estimation",
    aliases: ["extremum estimation","extremum estimator","m estimator"],
    modules: ["Causalean/Stat/EmpiricalProcess/","Causalean/Stat/MEstimation/"],
  },
  {
    canonical: "manski bounds",
    aliases: ["manski worst case bounds","no assumption bounds","no assumptions bounds","worst case bounds"],
    modules: ["Causalean/PO/ID/Partial/Manski/"],
  },
  {
    canonical: "marginal treatment effect",
    aliases: ["mte"],
    modules: ["Causalean/Estimation/NPIV/","Causalean/PO/ID/Exact/VariableIntensityIV/"],
  },
  {
    canonical: "mediator",
    aliases: ["intermediate variable","intervening variable","mediating variable"],
    modules: ["Causalean/PO/ID/Exact/","Causalean/SCM/ID/"],
  },
  {
    canonical: "minimax lower bound",
    aliases: ["assouad lower bound","fano lower bound","le cam lower bound","minimax risk lower bound","testing lower bound","two point lower bound","worst case lower bound"],
    modules: ["Causalean/Estimation/StructureAgnostic/","Causalean/Stat/Minimax/"],
  },
  {
    canonical: "minimax rate",
    aliases: ["convergence rate","lower bound rate","minimax","minimax optimal rate","minimax rate threshold","optimal rate","rate optimality"],
    modules: ["Causalean/Estimation/StructureAgnostic/","Causalean/Stat/","Causalean/Stat/Minimax/"],
  },
  {
    canonical: "monotone instrumental variable",
    aliases: ["miv"],
    modules: ["Causalean/PO/ID/Partial/Manski/"],
  },
  {
    canonical: "monotone treatment response",
    aliases: ["monotone response","mtr"],
    modules: ["Causalean/PO/ID/Partial/Manski/"],
  },
  {
    canonical: "monotone treatment selection",
    aliases: ["mts"],
    modules: ["Causalean/PO/ID/Partial/Manski/"],
  },
  {
    canonical: "monotonicity",
    aliases: ["iv monotonicity","monotonicity assumption","no defiers"],
    modules: ["Causalean/PO/ID/Exact/VariableIntensityIV/","Causalean/PO/ID/Exact/LATE","Causalean/PO/ID/Exact/MultipleInstrumentIV/"],
  },
  {
    canonical: "natural mediation effects",
    aliases: ["natural direct and indirect effects","natural direct effect","natural indirect effect","nde","nie"],
    modules: ["Causalean/PO/ID/Exact/Frontdoor","Causalean/SCM/ID/"],
  },
  {
    canonical: "never treated controls",
    aliases: ["never treated cohort","never treated comparison group"],
    modules: ["Causalean/PO/ID/Exact/CSDID.lean","Causalean/Panel/AdoptionPath.lean","Causalean/Panel/EstimandCharacterization/StaggeredTWFEDecomposition/","Causalean/Panel/EstimandCharacterization/EventStudyContamination/"],
  },
  {
    canonical: "neyman orthogonality",
    aliases: ["locally robust moment","locally robust score","orthogonal moment","orthogonal score"],
    modules: ["Causalean/Estimation/Efficiency/","Causalean/Estimation/OrthogonalMoments/"],
  },
  {
    canonical: "nonparametric instrumental variables",
    aliases: ["non parametric instrumental variables","non parametric iv","nonparametric instrumental variable","nonparametric iv","npiv"],
    modules: ["Causalean/Estimation/NPIV/","Causalean/SCM/Examples/"],
  },
  {
    canonical: "not yet treated controls",
    aliases: ["not yet treated comparison group"],
    modules: ["Causalean/PO/ID/Exact/CSDID.lean","Causalean/Panel/AdoptionPath.lean","Causalean/Panel/EstimandCharacterization/EventStudyContamination/"],
  },
  {
    canonical: "nuisance estimation",
    aliases: ["first stage estimation","nuisance function estimation","nuisance learning","nuisance parameter estimation"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Estimation/CATE/","Causalean/Estimation/OSL/"],
  },
  {
    canonical: "omitted variable bias",
    aliases: ["cinelli hazlett bias","ovb","unobserved confounding bias"],
    modules: ["Causalean/Estimation/StructureAgnostic/","Causalean/PO/ID/Partial/SupportFunction/"],
  },
  {
    canonical: "one step estimator",
    aliases: ["one step correction","one step update"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/OrthogonalMoments/"],
  },
  {
    canonical: "overlap",
    aliases: ["common support","covariate overlap","positivity","propensity bounded away from zero and one","strict overlap","weak overlap"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Estimation/DTR/","Causalean/PO/ID/","Causalean/SCM/ID/Overlap","Causalean/Stat/PolynomialTail/"],
  },
  {
    canonical: "parallel trends",
    aliases: ["common trend assumption","common trends","common trends assumption","parallel trend assumption","parallel trends assumption"],
    modules: ["Causalean/PO/ID/Exact/CSDID.lean","Causalean/PO/ID/Exact/DID.lean","Causalean/Panel/EstimandCharacterization/EventStudyContamination/","Causalean/Panel/EstimandCharacterization/FlexibleDIDMundlak/"],
  },
  {
    canonical: "partial identification",
    aliases: ["bounds","identified set","manski bounds","set identification","sharp bounds"],
    modules: ["Causalean/PO/ID/Partial/"],
  },
  {
    canonical: "plug in estimator",
    aliases: ["plug in estimation","plugin estimation","plugin estimator"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/OSL/"],
  },
  {
    canonical: "potential outcome",
    aliases: ["counterfactual","outcome schedule","potential outcomes"],
    modules: ["Causalean/PO/"],
  },
  {
    canonical: "pre trends",
    aliases: ["pre treatment trends","pretreatment trends","pretrends"],
    modules: ["Causalean/Panel/EstimandCharacterization/EventStudyContamination/"],
  },
  {
    canonical: "principal stratification",
    aliases: ["principal strata","principal strata analysis","principal stratum"],
    modules: ["Causalean/PO/ID/Exact/MultipleInstrumentIV/","Causalean/PO/ID/Partial/Lee/"],
  },
  {
    canonical: "propensity score",
    aliases: ["assignment probability","assignment propensity","propensity","propensity function","treatment assignment score","treatment probability","treatment propensity score"],
    modules: ["Causalean/Estimation/","Causalean/Estimation/ATE/","Causalean/Estimation/ATT/","Causalean/Estimation/CATE/","Causalean/Estimation/DTR/","Causalean/PO/ID/"],
  },
  {
    canonical: "proximal inference",
    aliases: ["proximal causal inference","proximal identification","proximal","negative controls","negative control","negative control proxies","negative control variables","negative control outcome","negative control exposure","proxy variables","proxy","proxies","proxy controls","proxy covariates","outcome proxy","treatment proxy"],
    modules: ["Causalean/PO/ID/Exact/Proximal/","Causalean/PO/ID/Partial/Proxy/"],
  },
  {
    canonical: "rademacher complexity",
    aliases: ["rademacher average","rademacher averages","rademacher complexity bound"],
    modules: ["Causalean/Stat/Concentration/","Causalean/Stat/EmpiricalProcess/"],
  },
  {
    canonical: "regression discontinuity",
    aliases: ["cutoff","discontinuity","rd design","rdd","running variable"],
    modules: ["Causalean/PO/ID/Exact/"],
  },
  {
    canonical: "rosenbaum bounds",
    aliases: ["rosenbaum sensitivity bounds"],
    modules: ["Causalean/PO/ID/Exact/","Causalean/PO/ID/Partial/SupportFunction/"],
  },
  {
    canonical: "sample splitting",
    aliases: ["sample split","split sample estimation"],
    modules: ["Causalean/Estimation/OSL/","Causalean/Estimation/OrthogonalMoments/"],
  },
  {
    canonical: "semiparametric efficiency bound",
    aliases: ["efficiency bound","efficient variance bound","hahn bound","semiparametric variance bound"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/Efficiency/"],
  },
  {
    canonical: "sensitivity analysis",
    aliases: ["robustness analysis","sensitivity bounds"],
    modules: ["Causalean/PO/ID/Partial/SupportFunction/"],
  },
  {
    canonical: "sharp bounds",
    aliases: ["sharp identified bounds"],
    modules: ["Causalean/PO/ID/Partial/","Causalean/PO/ID/Partial/SupportFunction/"],
  },
  {
    canonical: "stabilized weights",
    aliases: ["stabilised inverse probability weights","stabilised ipw weights","stabilised weights","stabilized inverse probability weights","stabilized ipw weights"],
    modules: ["Causalean/Estimation/ATE/","Causalean/Estimation/ATT/"],
  },
  {
    canonical: "staggered adoption",
    aliases: ["staggered implementation","staggered rollout","staggered treatment adoption","staggered treatment timing"],
    modules: ["Causalean/PO/ID/Exact/CSDID.lean","Causalean/Panel/AdoptionPath.lean","Causalean/Panel/EstimandCharacterization/"],
  },
  {
    canonical: "structural causal model",
    aliases: ["generalized structural causal model","gscm","scm","sem","structural equation model"],
    modules: ["Causalean/SCM/","Causalean/SCM/Model/"],
  },
  {
    canonical: "sun abraham",
    aliases: ["interaction weighted event study","iw estimator","iw event study","sun and abraham"],
    modules: ["Causalean/Panel/EstimandCharacterization/EventStudyContamination/"],
  },
  {
    canonical: "sutva",
    aliases: ["no interference","noninterference","stable unit treatment value assumption"],
    modules: ["Causalean/PO/Conditioning/","Causalean/PO/ID/Exact/"],
  },
  {
    canonical: "swig",
    aliases: ["single world intervention graph","single world intervention graphs"],
    modules: ["Causalean/Graph/","Causalean/SCM/"],
  },
  {
    canonical: "synthetic control",
    aliases: ["synthetic control method","synthetic controls"],
    modules: ["Causalean/Panel/"],
  },
  {
    canonical: "tail behavior",
    aliases: ["tail behaviour","tail condition","tail decay","tail regularity"],
    modules: ["Causalean/Estimation/","Causalean/Stat/Concentration/"],
  },
  {
    canonical: "tmle",
    aliases: ["targeted maximum likelihood estimation","targeted maximum likelihood estimator","targeted minimum loss estimation","targeted minimum loss estimator"],
    modules: ["Causalean/Estimation/"],
  },
  {
    canonical: "transportability",
    aliases: ["external validity","generalizability","population transportability","transportable causal effect"],
    modules: ["Causalean/Estimation/","Causalean/Graph/DSep/","Causalean/SCM/ID/"],
  },
  {
    canonical: "two way fixed effects",
    aliases: ["twfe","two way fixed effect"],
    modules: ["Causalean/Panel/EstimandCharacterization/HeterogeneousTWFE/","Causalean/Panel/EstimandCharacterization/StaggeredTWFEDecomposition/","Causalean/Panel/EstimandCharacterization/FlexibleDIDMundlak/","Causalean/Panel/FixedEffect.lean","Causalean/Panel/FixedEffect/"],
  },
  {
    canonical: "u statistic",
    aliases: ["u stat","u statistics"],
    modules: ["Causalean/Stat/UStatistic/"],
  },
  {
    canonical: "valid bounds",
    aliases: ["outer bounds","valid outer bounds"],
    modules: ["Causalean/PO/ID/Partial/"],
  },
  {
    canonical: "weak overlap",
    aliases: ["limited overlap","near violation of overlap","poor overlap","weak positivity"],
    modules: ["Causalean/Estimation/"],
  },
  {
    canonical: "z estimation",
    aliases: ["estimating equation estimator","root of an estimating equation","z estimator"],
    modules: ["Causalean/Stat/GMM/","Causalean/Stat/MEstimation/"],
  },

  // --- Causal discovery / structure identification family (structure-ID mode) ---
  {
    canonical: "causal discovery",
    aliases: ["structure learning","causal structure learning","structure identification","graph recovery","causal graph recovery"],
    modules: ["Causalean/Discovery/","Causalean/Graph/MarkovEquiv"],
  },
  {
    canonical: "darmois skitovich",
    aliases: ["darmois skitovich theorem","ds theorem","independent linear form"],
    modules: ["Causalean/Mathlib/Probability/DarmoisSkitovich","Causalean/Discovery/LiNGAM/"],
  },
  {
    canonical: "linear non gaussian acyclic model",
    aliases: ["lingam","linear non gaussian","non gaussian scm","ica lingam","direct lingam"],
    modules: ["Causalean/Discovery/LiNGAM/","Causalean/Discovery/LinearDisentanglement","Causalean/Mathlib/Probability/DarmoisSkitovich"],
  },
  {
    canonical: "linear causal disentanglement",
    aliases: ["causal disentanglement","linear disentanglement","identifiability up to sign and permutation"],
    modules: ["Causalean/Discovery/LinearDisentanglement","Causalean/Discovery/"],
  },
  {
    canonical: "additive noise model",
    aliases: ["anm","additive noise","post nonlinear model","independent residual identifiability"],
    modules: ["Causalean/Discovery/"],
  },
  {
    canonical: "markov equivalence",
    aliases: ["markov equivalence class","mec","essential graph","cpdag","observationally equivalent dags","covered edge"],
    modules: ["Causalean/Graph/MarkovEquiv","Causalean/Graph/"],
  },
];

export interface AliasExpansion {
  /** Extra surface terms (canonical + synonyms of matched concepts) to widen the query. */
  terms: string[];
  /** Module path prefixes suggested by matched concepts (module-level fallback). */
  modules: string[];
  /** Canonical concepts that matched the query (debug / display). */
  concepts: string[];
}

/**
 * Find every alias entry whose canonical or any synonym occurs in `text`, and return
 * the union of their surface forms (as expansion terms), suggested modules, and the
 * matched canonical concepts. Single-word forms match on whole-word boundaries;
 * multi-word forms match as substrings. Returns empty arrays when nothing matches.
 */
export function expandQuery(text: string): AliasExpansion {
  const padded = " " + normalizeConcept(text) + " ";
  const terms = new Set<string>();
  const modules = new Set<string>();
  const concepts = new Set<string>();
  for (const e of CAUSAL_ALIASES) {
    const forms = [e.canonical, ...e.aliases];
    // why: uppercase IF is an abbreviation; lowercase "if" is ordinary English.
    const hit = (e.canonical === "influence function" && /\bIF\b/.test(text)) || forms.some((f) => {
      const nf = normalizeConcept(f);
      return nf.includes(" ") ? padded.includes(nf) : padded.includes(" " + nf + " ");
    });
    if (!hit) continue;
    concepts.add(e.canonical);
    for (const f of forms) terms.add(normalizeConcept(f));
    for (const m of e.modules) modules.add(m);
  }
  return { terms: [...terms], modules: [...modules], concepts: [...concepts] };
}
