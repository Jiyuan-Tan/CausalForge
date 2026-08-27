node covariate-line | Covariate line | pretreatment X
node active-block | Active block Bₙ | small covariate mass
node contrast | Local contrast | size hₙ, two signs
node joint-decay | Joint decay | caps weak-arm mass
node weak-arm | Weak arm | probability qₙ on Bₙ
node hard-signs | Signs hard to tell | little arm information
node rate-question | Rate question | how small may hₙ be
edge covariate-line -> active-block
edge active-block -> contrast
edge active-block -> weak-arm
edge joint-decay -> weak-arm
edge contrast -> hard-signs
edge weak-arm -> hard-signs
edge hard-signs -> rate-question
