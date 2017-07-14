#### nouns
### indefinite articles; eliminate
%n_adj_indef :: a [pos=a,-def] [pos=n] ; // 0:2
%n_indef :: a [pos=n,-def] ; // 0:1
### definite articles
%n_adj_def :: the [pos=a,+def] [pos=n] ; // 0:1
%n_def :: the [pos=n,+def] ; // 0:1
### possessives
%n_my :: my [pos=n,poss=[+expl,+p1,-plr],+def] ; // 0:1

#### verbs

### verb objects; FIGURE OUT HOW TO HANDLE INDIRECT AND DIRECT OBJECTS
%v_1s_ob :: [pos=v,ob=[+expl,+p1,-plr]] me ; // 1:0
%v_2_ob :: [pos=v,ob=[+expl,+p2]] you ; // 1:0
%v_3sn_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr,-fem]] it ; // 1:0
%v_3sm_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr,-fem]] him ; // 1:0
%v_3sf_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr,+fem]] her ; // 1:0
%v_1p_ob :: [pos=v,ob=[+expl,+p1,+plr]] us ; // 1:0
%v_3p_ob :: [pos=v,ob=[+expl,-p1,-p2,+plr,-fem]] them ; // 1:0

#### verbs with definite objects; has to happen before must/should etc. because they make nouns out of verbs
$v_defsing_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr]] [pos=n,+def,+acc,rl=[+acc],-plr] ; >< 0 1

### negative
## must
%v_neg_1s_must :: i must_v[pos=v,+aux,+neg,sb=[+expl,+p1,-plr]] not [pos=v,tam=stm] ; 3-> [pos=n] ; // 0:3 2:3
## can, could
%v_neg_1s_can :: i can_v[+neg,sb=[+expl,+p1,-plr],tm=imf] not [pos=v,sb=[+expl,+p1,-plr]] ; // 0:3 2:3
## should
%v_neg_1s_should :: i shall_v[pos=v,+neg,tam=pst,+aux,sb=[+expl,+p1,-plr]] not [pos=v,tam=stm] ; 2-> [pos=n] ; // 0:3 2:3
## present
%v_neg_1s_prs :: i do not [pos=v,+neg,sb=[+p1,-plr,+expl],tm=imf] ; // 0:3 1:3 2:3
%v_neg_2_prs :: you do not [pos=v,+neg,sb=[+expl,+p2],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sm_prs :: he does not [pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sf_prs :: she does not [pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_prs :: we do not [pos=v,+neg,sb=[+expl,+p1,+plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_prs :: they do not [pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; // 0:3 1:3 2:3
## past
%v_neg_1s_pst :: i did not [pos=v,+neg,sb=[+expl,+p1,-plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_2_pst :: you did not [pos=v,+neg,sb=[+expl,+p2],tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sm_pst :: he did not [pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sf_pst :: she did not [pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_1p_pst :: we did not [pos=v,+neg,sb=[+expl,+p1,+plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_1p_pst :: they did not [pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=prf] ; // 0:3 1:3 2:3
## future will (use imperfective)
%v_neg_1s_fut :: i will not [pos=v,+neg,sb=[+expl,+p1,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_2_fut :: you will not [pos=v,+neg,sb=[+expl,+p2],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sm_fut :: he will not [pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sf_fut :: she will not [pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_fut :: we will not [pos=v,+neg,sb=[+expl,+p1,+plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_fut :: they will not [pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; // 0:3 1:3 2:3
## future going to; most follow auxiliary cases
%v_neg_1s_gt_fut :: i am not going to [pos=v,+neg,sb=[+expl,+p1,-plr],tm=imf] ; // 0:5 1:5 2:5 3:5 4:5
%v_neg_2_gt_fut :: you are not going to [pos=v,+neg,sb=[+expl,+p2],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_3sm_gt_fut :: he is not going to [pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_3sf_gt_fut :: she is not going to [pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_1p_gt_fut :: we are not going to [pos=v,+neg,sb=[+expl,+p1,+plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_1p_gt_fut :: they will not [pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
## present perfect (perfective in negative)
%v_neg_1s_prsprf :: i have not [pos=v,+neg,sb=[+expl,+p1,-plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_2_prsprf :: you have not [pos=v,+neg,sb=[+expl,+p2],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sm_prsprf :: he has not [pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sf_prsprf :: she has not [pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_1p_prsprf :: we have not [pos=v,+neg,sb=[+expl,+p1,+plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_1p_prsprf :: they have not [pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
## present continuous (imperfective in negative)
%v_neg_1s_cont :: i am not [pos=v,+neg,sb=[+expl,+p1,-plr],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_2_cont :: you are not [pos=v,+neg,sb=[+expl,+p2],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sm_cont :: he is not [pos=v,+neg,sb=[+expl,-p1,-p2,-plr,-fem],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sf_cont :: she is not [pos=v,+neg,sb=[+expl,-p1,-p2,-plr,+fem],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_cont :: we are not [pos=v,+neg,sb=[+expl,+p1,+plr],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_3p_cont :: they are not [pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=ing,tm=imf] ; // 0:3 1:3 2:3
## past continuous
%v_neg_1s_cont :: i be_v[pos=v,+aux,-prosp] not [pos=v,+neg,sb=[+expl,+p1,-plr],tam=ing] ; // 0:3 2:3
## ?used to
## future continuous
## past perfect
%v_neg_1s_pstprf :: i have_v[pos=v,tam=pst,+aux] not [pos=v,+neg,sb=[+expl,+p1,-plr],tam=pp] ; // 0:3 2:3
%v_neg_2_pstprf :: you have_v[pos=v,tam=pst,+aux] not [pos=v,+neg,sb=[+p2],tam=pp] ; // 0:3 2:3
%v_neg_3sf_pstprf :: she have_v[pos=v,tam=pst,+aux] not [pos=v,+neg,sb=[-p1,-p2,+fem,-plr],tam=pp] ; // 0:3 2:3
## conditional
## conditional perfect
## have to present
## have to past
## about to

### affirmative
## should
%v_1s_should :: i shall_v[pos=v,tam=pst,+aux,sb=[+expl,+p1,-plr]] [pos=v,tam=stm] ; 2-> [pos=n] ; // 0:2
## must
%v_1s_must :: i must_v[pos=v,+aux,sb=[+expl,+p1,-plr]] [pos=v,tam=stm] ; 2-> [pos=n] ; // 0:2
## have to present
## have to past
## can, could
## future will
%v_1s_fut :: i will [pos=v,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:2 1:2
## future going to
%v_1s_gt_fut :: i am going to [pos=v,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:4 1:4 2:4 3:4
## present perfect (use gerundive+al)
%v_1s_prsprf :: i have [pos=v,sb=[+expl,+p1,-plr],tam=pp,tm=ger,ax=al] ; // 0:2 1:2
%v_2_prsprf :: you have [pos=v,sb=[+expl,+p2],tam=pp,tm=ger,ax=al] ; // 0:2 1:2
%v_3sm_prsprf :: he has [pos=v,sb=[+expl,-p1,-p2,-fem,-plr],tam=pp,tm=ger,ax=al] ; // 0:2 1:2
%v_3sf_prsprf :: she has [pos=v,sb=[+expl,-p1,-p2,+fem,-plr],tam=pp,tm=ger,ax=al] ; // 0:2 1:2
%v_1p_prsprf :: we have [pos=v,sb=[+expl,+p1,+plr],tam=pp,tm=ger,ax=al] ; // 0:2 1:2
%v_1p_prsprf :: they have [pos=v,sb=[+expl,-p1,-p2,+plr],tam=pp,tm=ger,ax=al] ; // 0:1 1:2
## present continuous ; have to figure out a way to get new in there after the verb
%v_1s_cont :: i be_v[pos=v,+aux,-prosp] [pos=v,sb=[+expl,+p1,-plr],tam=ing] ; // 0:2
## used to
%v_1s_usedto :: i use_v[pos=v,tam=pst,+aux] to [pos=v,sb=[+expl,+p1,-plr],tam=stm] ; // 0:3 2:3
## past perfect
%v_1s_pstprf :: i have_v[pos=v,tam=pst,+aux] [pos=v,sb=[+expl,+p1,-plr],tam=pp] ; // 0:2
## conditional
## conditional perfect
## about to pres./past (prospective)
%v_1s_prosp :: i be_v[pos=v,+aux,+prosp] about to [pos=v,sb=[+expl,+p1,-plr],tam=stm] ; // 0:4 2:4 3:4
## present ; must follow auxiliary cases
%v_1s_prs :: i [pos=v,tam=stm,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:1
%v_2_prs :: you [pos=v,tam=stm,sb=[+expl,+p2],tm=imf,ax=al] ; // 0:1
%v_3sm_prs :: he [pos=v,tam=prs,sb=[+expl,-p1,-p2,-plr,-fem],tm=imf,ax=al] ; // 0:1
%v_3sf_prs :: she [pos=v,tam=prs,sb=[+expl,-p1,-p2,-plr,+fem],tm=imf,ax=al] ; // 0:1
%v_3sn_prs :: it [pos=v,tam=prs,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf,ax=al] ; // 0:1
%v_1p_prs :: we [pos=v,tam=stm,sb=[+expl,+p1,+plr],tm=imf,ax=al] ; // 0:1
%v_3p_prs :: they [pos=v,tam=stm,sb=[+expl,-p1,-p2,+plr],tm=imf,ax=al] ; // 0:1
## past
%v_1s_pst :: i [pos=v,tam=pst,sb=[+expl,+p1,-plr],tm=prf] ; // 0
%v_2_pst :: you [pos=v,tam=pst,sb=[+expl,+p2],tm=prf] ; // 0
%v_3sm_pst :: he [pos=v,tam=pst,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0
%v_3sf_pst :: she [pos=v,tam=pst,sb=[+expl,-p1,-p2,+fem,-plr],tm=prf] ; // 0
%v_1p_pst :: we [pos=v,tam=pst,sb=[+expl,+p1,+plr],tm=prf] ; // 0
%v_3p_pst :: they [pos=v,tam=pst,sb=[+expl,-p1,-p2,+plr],tm=prf] ; // 0
%v_3sn_pst :: it [pos=v,tam=pst,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0

## jussive (this has to follow the above because of "he will/can/ought to... let me go")
%v_1ps_jus :: let me [pos=v,tam=stm,sb=[+expl,+p1,-plr],tm=j_i] ; // 0:2 1:2

### infinitive

### aux verb (no subject)
## future will
## future going to
## present perfect
## present continuous
## used to
## past perfect
## conditional
## conditional perfect
## should
## must
## can, could
## about to

### be
## negative
%v_neg_1s_am :: i be_v[pos=v,+neg,sb=[+expl,+p1,-plr],tam=prs,tm=imf] not ; // 0 2
%v_neg_3sm_is :: he be_v[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tam=prs,tm=imf] not ; // 0 2
%v_neg_3sf_is :: she be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=prs,tm=imf] not ; // 0 2
%v_net_3sn_is :: it be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=prs,tm=imf] not ; // 0 2
%v_neg_2_are :: you be_v[pos=v,+neg,sb=[+expl,+p2],tam=prs,tm=imf] not ; // 0 2
%v_neg_1p_are :: we be_v[pos=v,+neg,sb=[+expl,+p1,+plr],tam=prs,tm=imf] not ; // 0 2
%v_neg_3p_are :: they be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=prs,tm=imf] not ; // 0 2
%v_neg_1s_was :: i be_v[pos=v,+neg,sb=[+expl,+p1,-plr],tam=pst,tm=prf] not ; // 0 2
%v_neg_3sm_was :: he be_v[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tam=pst,tm=prf] not ; // 0 2
%v_neg_3sf_was :: she be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=pst,tm=prf] not ; // 0 2
%v_neg_2_were :: you be_v[pos=v,+neg,sb=[+expl,+p2],tam=pst,tm=prf] not ; // 0 2
%v_neg_1p_were :: we be_v[pos=v,+neg,sb=[+expl,+p1,+plr],tam=pst,tm=prf] not ; // 0 2
%v_neg_3p_were :: they be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=pst,tm=prf] not ; // 0 2
%v_neg_is :: be_v[pos=v,+neg,sb=[+expl,-p1,-p2,-plr],tam=prs,tm=imf] not ; // 1
%v_neg_are :: be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=prs,tm=imf] not ; // 1
## affirmative
# present
%v_1s_am :: i be_v[pos=v,sb=[+expl,+p1,-plr],tam=prs,tm=imf,-aux] ; // 0
%v_3sm_is :: he be_v[pos=v,sb=[+expl,-p1,-p2,-fem,-plr],tam=prs,tm=imf,-aux] ; // 0
%v_3sf_is :: she be_v[pos=v,sb=[+expl,-p1,-p2,+fem,-plr],tam=prs,tm=imf,-aux] ; // 0
%v_2_are :: you be_v[pos=v,sb=[+expl,+p2],tam=prs,tm=imf,-aux] ; // 0
%v_1p_are :: we be_v[pos=v,sb=[+expl,+p1,+plr],tam=prs,tm=imf,-aux] ; // 0
%v_3p_are :: they be_v[pos=v,sb=[+expl,-p1,-p2,+plr],tam=prs,tm=imf,-aux] ; // 0
%v_is :: be_v[pos=v,sb=[+expl,-p1,-p2,-plr],tam=prs,tm=imf,-aux]
%v_are :: be_v[pos=v,sb=[+expl,-p1,-p2,+plr],tam=prs,tm=imf,-aux]
# past
%v_1s_was :: i be_v[pos=v,sb=[+expl,+p1,-plr],tam=pst,tm=prf,-aux] ; // 0
%v_3sm_was :: he be_v[pos=v,sb=[+expl,-p1,-p2,-fem,-plr],tam=pst,tm=prf,-aux] ; // 0
%v_3sf_was :: she be_v[pos=v,sb=[+expl,-p1,-p2,+fem,-plr],tam=pst,tm=prf,-aux] ; // 0
%v_2_were :: you be_v[pos=v,sb=[+expl,+p2],tam=pst,tm=prf,-aux] ; // 0
%v_1p_were :: we be_v[pos=v,sb=[+expl,+p1,+plr],tam=pst,tm=prf,-aux] ; // 0
%v_3p_were :: they be_v[pos=v,sb=[+expl,-p1,-p2,+plr],tam=pst,tm=prf,-aux] ; // 0
# future (use hone)
%v_1s_willbe :: i will be_v[pos=v,sb=[+expl,+p1,-plr],tam=stm,tm=fut,-aux] ; // 0:2 1:2
%v_3sm_willbe :: he will be_v[pos=v,sb=[+expl,-p1,-p2,-fem,-plr],tam=stm,tm=fut,-aux] ; // 0:2 1:2
%v_3sf_willbe :: she will be_v[pos=v,sb=[+expl,-p1,-p2,+fem,-plr],tam=stm,tm=fut,-aux] ; // 0:2 1:2
%v_2_willbe :: you will be_v[pos=v,sb=[+expl,+p2],tam=stm,tm=fut,-aux] ; // 0:2 1:2
%v_1p_willbe :: we will be_v[pos=v,sb=[+expl,+p1,+plr],tam=stm,tm=fut,-aux] ; // 0:2 1:2
%v_3p_willbe :: they will be_v[pos=v,sb=[+expl,-p1,-p2,+plr],tam=stm,tm=fut,-aux] ; // 0:1 1:2

## passive / pp adjectives (by for ambiguous cases?)

### other stem forms (all present?)

### other pp forms

