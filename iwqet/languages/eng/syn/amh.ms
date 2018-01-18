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

### BE can't take an object
%v_be :: be_v[ob=[-expl]]

### verb objects; FIGURE OUT HOW TO HANDLE INDIRECT AND DIRECT OBJECTS
%v_1s_ob :: [pos=v,ob=[+expl,+p1,-plr]] me ; // 1:0
%v_2_ob :: [pos=v,ob=[+expl,+p2]] you ; // 1:0
%v_3sn_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr,-fem]] it ; // 1:0
%v_3sm_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr,-fem]] him ; // 1:0
%v_3sf_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr,+fem]] her ; // 1:0
%v_1p_ob :: [pos=v,ob=[+expl,+p1,+plr]] us ; // 1:0
%v_3p_ob :: [pos=v,ob=[+expl,-p1,-p2,+plr,-fem]] them ; // 1:0

#### LEAVE THIS (FOR NOW?) BECAUSE OF THE CONFUSION ASSOCIATED WITH SWAPPING IN MORPHOSYNS
#### verbs with definite objects
## make the object accusative and swap it with the verb
#### has to follow pronoun subjects + verbs and precede must/should etc. because they make nouns out of verbs
## $v_defsing_ob :: [pos=v,ob=[+expl,-p1,-p2,-plr]] [pos=n,+def,cs=acc,-plr] ; >< 0 1

### negative modals
## must
#%v_neg_1s_must :: i must_v[pos=v,+aux,+neg,sb=[+expl,+p1,-plr]] [pos=adv,+neg] [pos=v,tam=stm] ; 3-> [pos=n] ; // 0:3 2:3
## can, could
#%v_neg_1s_can :: i can_v[+neg,sb=[+expl,+p1,-plr],tm=imf] [pos=adv,+neg] [pos=v,sb=[+expl,+p1,-plr]] ; // 0:3 2:3
## should
#%v_neg_1s_should :: i shall_v[pos=v,+neg,tam=pst,+aux,sb=[+expl,+p1,-plr]] [pos=adv,+neg] [pos=v,tam=stm] ; 2-> [pos=n] ; // 0:3 2:3


### infinitive

### aux verb (no subject)
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
## about to pres./past (prospective)
%v_1s_prosp :: i be_v[pos=v,+aux,+prosp] about to [pos=v,sb=[+expl,+p1,-plr],tam=stm] ; // 0:4 2:4 3:4
%v_2_prosp :: you be_v[pos=v,+aux,+prosp] about to [pos=v,sb=[+expl,-p1,+p2],tam=stm] ; // 0:4 2:4 3:4
%v_3sm_prosp :: he be_v[pos=v,+aux,+prosp] about to [pos=v,sb=[+expl,-p1,-p2,-fem,-plr],tam=stm] ; // 0:4 2:4 3:4
%v_3sf_prosp :: she be_v[pos=v,+aux,+prosp] about to [pos=v,sb=[+expl,-p1,-p2,+fem,-plr],tam=stm] ; // 0:4 2:4 3:4
%v_1p_prosp :: we be_v[pos=v,+aux,+prosp] about to [pos=v,sb=[+expl,+p1,+plr],tam=stm] ; // 0:4 2:4 3:4
%v_3p_prosp :: they be_v[pos=v,+aux,+prosp] about to [pos=v,sb=[+expl,-p1,-p2,+plr],tam=stm] ; // 0:4 2:4 3:4
## going to
%v_neg_1s_gt_fut :: i am [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,+p1,-plr],tm=imf] ; // 0:5 1:5 2:5 3:5 4:5
%v_neg_2_gt_fut :: you are [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,+p2],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_3sm_gt_fut :: he is [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_3sf_gt_fut :: she is [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_1p_gt_fut :: we are [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,+p1,+plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_3p_gt_fut :: they are [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_1s_gt_fut :: i am going to [pos=v,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:4 1:4 2:4 3:4
%v_2_gt_fut :: you are going to [pos=v,sb=[+expl,+p2],tm=imf,ax=al] ; // 0:4 1:4 2:4 3:4
%v_3sf_gt_fut :: she is going to [pos=v,sb=[+expl,-p1,-p2,-plr,+fem],tm=imf,ax=al] ; // 0:4 1:4 2:4 3:4
%v_3sm_gt_fut :: he is going to [pos=v,sb=[+expl,-p1,-p2,-plr,-fem],tm=imf,ax=al] ; // 0:4 1:4 2:4 3:4
%v_1p_gt_fut :: we are going to [pos=v,sb=[+expl,+p1,+plr],tm=imf,ax=al] ; // 0:4 1:4 2:4 3:4
%v_3p_gt_fut :: they are going to [pos=v,sb=[+expl,-p1,-p2,+plr],tm=imf,ax=al] ; // 0:4 1:4 2:4 3:4
%v_neg_3ss_gt_fut :: is [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,-p1,-p2,-plr],tm=imf] ; //  0:4 1:4 2:4 3:4
%v_neg_3pp_gt_fut :: are [pos=adv,+neg] going to ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; //  0:4 1:4 2:4 3:4

### be
## negative
%v_neg_1s_am :: i be_v[pos=v,+neg,sb=[+expl,+p1,-plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_3sm_is :: he be_v[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_3sf_is :: she be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 0:1 2:1
%v_net_3sn_is :: it be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_2_are :: you be_v[pos=v,+neg,sb=[+expl,+p2],tam=prs,tm=imf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_1p_are :: we be_v[pos=v,+neg,sb=[+expl,+p1,+plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_3p_are :: they be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_1s_was :: i be_v[pos=v,+neg,sb=[+expl,+p1,-plr],tam=pst,tm=prf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_3sm_was :: he be_v[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tam=pst,tm=prf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_3sf_was :: she be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=pst,tm=prf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_2_were :: you be_v[pos=v,+neg,sb=[+expl,+p2],tam=pst,tm=prf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_1p_were :: we be_v[pos=v,+neg,sb=[+expl,+p1,+plr],tam=pst,tm=prf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_3p_were :: they be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=pst,tm=prf] [pos=adv,+neg] ; // 0:1 2:1
%v_neg_is :: be_v[pos=v,+neg,sb=[+expl,-p1,-p2,-plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 1
%v_neg_are :: be_v[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=prs,tm=imf] [pos=adv,+neg] ; // 1
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

### adverbs between subject and verb
%v_neg_1s_prs_adv :: i do [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+p1,-plr,+expl],tm=imf] ; // 0:3 1:3 2:3
%v_neg_2_prs_adv :: you do [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p2],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sm_prs_adv :: he does [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sf_prs_adv :: she does [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_prs_adv :: we do [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,+plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_prs_adv :: they do [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1s_pst_adv :: i did [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,-plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_2_pst_adv :: you did [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p2],tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sm_pst_adv :: he did [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sf_pst_adv :: she did [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_1p_pst_adv :: we did [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,+plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_3p_pst_adv :: they did [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=prf] ; // 0:3 1:3 2:3
%v_neg_1s_fut_adv :: i will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_2_fut_adv :: you will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p2],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sm_fut_adv :: he will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sf_fut_adv :: she will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_fut_adv :: we will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,+plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_fut_adv :: they will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_gt_fut_adv :: they will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; //  0:5 1:5 2:5 3:5 4:5
%v_neg_1s_prsprf_adv :: i have [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,-plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_2_prsprf_adv :: you have [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p2],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sm_prsprf_adv :: he has [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,-fem,-plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_3sf_prsprf_adv :: she has [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_1p_prsprf_adv :: we have [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,+plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_1p_prsprf_adv :: they have [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=pp,tm=prf] ; // 0:3 1:3 2:3
%v_neg_1s_cont_adv :: i am [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,-plr],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_2_cont_adv :: you are [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p2],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sm_cont_adv :: he is [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,-plr,-fem],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_3sf_cont_adv :: she is [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,-plr,+fem],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_1p_cont_adv :: we are [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,+plr],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_3p_cont_adv :: they are [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=ing,tm=imf] ; // 0:3 1:3 2:3
%v_neg_1s_cont_adv :: i be_v[pos=v,+aux,-prosp] [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,-plr],tam=ing] ; // 0:3 1:3 2:3
%v_neg_1s_pstprf :: i have_v[pos=v,tam=pst,+aux] [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,+p1,-plr],tam=pp] ; // 0:3 1:3 2:3
%v_neg_2_pstprf :: you have_v[pos=v,tam=pst,+aux] [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+p2],tam=pp] ; // 0:3 1:3 2:3
%v_neg_3sf_pstprf :: she have_v[pos=v,tam=pst,+aux] [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[-p1,-p2,+fem,-plr],tam=pp] ; // 0:3 1:3 2:3
%v_neg_3ss_prs_adv :: does [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,-plr],tm=imf] ; // 0:2 1:2
%v_neg_3pp_prs_adv :: do [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; // 0:2 1:2
%v_neg_pst_adv :: did [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=prf] ; // 0:2 1:2
%v_neg_fut_adv :: will [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tm=imf] ; // 0:2 1:2
%v_neg_3ss_prsprf_adv :: has [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+fem,-plr],tam=pp,tm=prf] ; // 0:2 1:2
%v_neg_3pp_prsprf_adv :: have [pos=adv,+neg] ([pos=adv]) ^[pos=v,+neg,sb=[+expl,-p1,-p2,+plr],tam=pp,tm=prf] ; // 0:2 1:2
### OTHER NEGATIVE VERBS
## past continuous
## ?used to
## future continuous
## past perfect
## conditional
## conditional perfect
## have to present
## have to past
## about to

### MOST AFFIRMATIVE VERBS
## future will (must precede other modals)
%v_1s_fut :: i will ([pos=adv]) ^[pos=v,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:2 1:2
%v_2_fut :: you will ([pos=adv]) ^[pos=v,sb=[+expl,+p],tm=imf,ax=al] ; // 0:2 1:2
%v_3sm_fut :: he will ([pos=adv]) ^[pos=v,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf,ax=al] ; // 0:2 1:2
%v_3sf_fut :: she will ([pos=adv]) ^[pos=v,sb=[+expl,-p1,-p2,+fem,-plr],tm=imf,ax=al] ; // 0:2 1:2
%v_1p_fut :: we will ([pos=adv]) ^[pos=v,sb=[+expl,+p1,+plr],tm=imf,ax=al] ; // 0:2 1:2
%v_3p_fut :: they will ([pos=adv]) ^[pos=v,sb=[+expl,-p1,-p2,+plr],tm=imf,ax=al] ; // 0:2 1:2
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
## present ; must follow auxiliary cases
%v_1s_prs :: i [pos=v,tam=prs,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:1
%v_2_prs :: you [pos=v,tam=prs,sb=[+expl,+p2],tm=imf,ax=al] ; // 0:1
%v_3sm_prs :: he [pos=v,tam=prs,sb=[+expl,-p1,-p2,-plr,-fem],tm=imf,ax=al] ; // 0:1
%v_3sf_prs :: she [pos=v,tam=prs,sb=[+expl,-p1,-p2,-plr,+fem],tm=imf,ax=al] ; // 0:1
%v_3sn_prs :: it [pos=v,tam=prs,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf,ax=al] ; // 0:1
%v_1p_prs :: we [pos=v,tam=prs,sb=[+expl,+p1,+plr],tm=imf,ax=al] ; // 0:1
%v_3p_prs :: they [pos=v,tam=prs,sb=[+expl,-p1,-p2,+plr],tm=imf,ax=al] ; // 0:1
## past
%v_1s_pst :: i [pos=v,tam=pst,sb=[+expl,+p1,-plr],tm=prf] ; // 0:1
%v_2_pst :: you [pos=v,tam=pst,sb=[+expl,+p2],tm=prf] ; // 0:1
%v_3sm_pst :: he [pos=v,tam=pst,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0:1
%v_3sf_pst :: she [pos=v,tam=pst,sb=[+expl,-p1,-p2,+fem,-plr],tm=prf] ; // 0:1
%v_1p_pst :: we [pos=v,tam=pst,sb=[+expl,+p1,+plr],tm=prf] ; // 0:1
%v_3p_pst :: they [pos=v,tam=pst,sb=[+expl,-p1,-p2,+plr],tm=prf] ; // 0:1
%v_3sn_pst :: it [pos=v,tam=pst,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0:1

%v_1s_gt_fut_adv :: i am going to [pos=adv] [pos=v,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:5 1:5 2:5 3:5
%v_1s_prsprf_adv :: i have [pos=adv] [pos=v,sb=[+expl,+p1,-plr],tam=pp,tm=ger,ax=al] ; // 0:3 1:3
%v_2_prsprf_adv :: you have [pos=adv] [pos=v,sb=[+expl,+p2],tam=pp,tm=ger,ax=al] ; // 0:3 1:3
%v_3sm_prsprf_adv :: he has [pos=adv] [pos=v,sb=[+expl,-p1,-p2,-fem,-plr],tam=pp,tm=ger,ax=al] ; // 0:3 1:3
%v_3sf_prsprf_adv :: she has [pos=adv] [pos=v,sb=[+expl,-p1,-p2,+fem,-plr],tam=pp,tm=ger,ax=al] ; // 0:3 1:3
%v_1p_prsprf_adv :: we have [pos=adv] [pos=v,sb=[+expl,+p1,+plr],tam=pp,tm=ger,ax=al] ; // 0:3 1:3
%v_1p_prsprf_adv :: they have [pos=adv] [pos=v,sb=[+expl,-p1,-p2,+plr],tam=pp,tm=ger,ax=al] ; // 0:1 1:3
%v_1s_cont_adv :: i be_v[pos=v,+aux,-prosp] [pos=adv] [pos=v,sb=[+expl,+p1,-plr],tam=ing] ; // 0:3
%v_1s_usedto_adv :: i use_v[pos=v,tam=pst,+aux] to [pos=adv] [pos=v,sb=[+expl,+p1,-plr],tam=stm] ; // 0:4 2:4
%v_1s_pstprf_adv :: i have_v[pos=v,tam=pst,+aux] [pos=adv] [pos=v,sb=[+expl,+p1,-plr],tam=pp] ; // 0:3
%v_1s_prs_adv :: i [pos=adv] [pos=v,tam=prs,sb=[+expl,+p1,-plr],tm=imf,ax=al] ; // 0:2
%v_2_prs_adv :: you [pos=adv] [pos=v,tam=prs,sb=[+expl,+p2],tm=imf,ax=al] ; // 0:2
%v_3sm_prs_adv :: he [pos=adv] [pos=v,tam=prs,sb=[+expl,-p1,-p2,-plr,-fem],tm=imf,ax=al] ; // 0:2
%v_3sf_prs_adv :: she [pos=adv] [pos=v,tam=prs,sb=[+expl,-p1,-p2,-plr,+fem],tm=imf,ax=al] ; // 0:2
%v_3sn_prs_adv :: it [pos=adv] [pos=v,tam=prs,sb=[+expl,-p1,-p2,-fem,-plr],tm=imf,ax=al] ; // 0:2
%v_1p_prs_adv :: we [pos=adv] [pos=v,tam=prs,sb=[+expl,+p1,+plr],tm=imf,ax=al] ; // 0:2
%v_3p_prs_adv :: they [pos=adv] [pos=v,tam=prs,sb=[+expl,-p1,-p2,+plr],tm=imf,ax=al] ; // 0:2
%v_1s_pst_adv :: i [pos=adv] [pos=v,tam=pst,sb=[+expl,+p1,-plr],tm=prf] ; // 0:2
%v_1s_adv_pst_adv :: i [pos=adv] [pos=adv] [pos=v,tam=pst,sb=[+expl,+p1,-plr],tm=prf] ; // 0:3
%v_2_pst_adv :: you [pos=adv] [pos=v,tam=pst,sb=[+expl,+p2],tm=prf] ; // 0:2
%v_3sm_pst_adv :: he [pos=adv] [pos=v,tam=pst,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0:2
%v_3sf_pst_adv :: she [pos=adv] [pos=v,tam=pst,sb=[+expl,-p1,-p2,+fem,-plr],tm=prf] ; // 0:2
%v_1p_pst_adv :: we [pos=adv] [pos=v,tam=pst,sb=[+expl,+p1,+plr],tm=prf] ; // 0:2
%v_3p_pst_adv :: they [pos=adv] [pos=v,tam=pst,sb=[+expl,-p1,-p2,+plr],tm=prf] ; // 0:2
%v_3sn_pst_adv :: it [pos=adv] [pos=v,tam=pst,sb=[+expl,-p1,-p2,-fem,-plr],tm=prf] ; // 0:2

# plural noun subject
%v_N3p_pst_adv :: [pos=n,+plr] ([pos=adv]) [pos=v,tam=pst,sb=[+expl,-p1,-p2,+plr],tm=prf]
%v_N3s_pst_adv :: [pos=n,-plr] ([pos=adv]) [pos=v,tam=pst,sb=[+expl,-p1,-p2,-plr],tm=prf]

### affirmative modals
## modals
%mod_1s :: i [pos=md,+aux,sb=[+expl,+p1,-plr]] [pos=v] ; // 0:1
%mod_2 :: you [pos=md,+aux,sb=[+expl,+p2]] [pos=v] ; // 0:1
%mod_3sm :: he [pos=md,+aux,sb=[+expl,-p1,-p2,-plr,-fem]] [pos=v] ; // 0:1
%mod_3sf :: she [pos=md,+aux,sb=[+expl,-p1,-p2,-plr,+fem]] [pos=v] ; // 0:1
%mod_1p :: we [pos=md,+aux,sb=[+expl,+p1,+plr]] [pos=v] ; // 0:1
%mod_3p :: they [pos=md,+aux,sb=[+expl,-p1,-p2,+plr]] [pos=v] ; // 0:1
#shall_v[pos=v,tam=pst,+aux,sb=[+expl,+p1,-plr]] [pos=v,tam=stm] ; 2-> [pos=n] ; // 0:2
## must
#%v_1s_must :: i must_v[pos=v,+aux,sb=[+expl,+p1,-plr]] [pos=v,tam=stm] ; 2-> [pos=n] ; // 0:2
## have to present
## have to past
## can, could

### negative modals
%mod_neg_1s :: i [pos=md,+aux,+neg,sb=[+expl,+p1,-plr]] [pos=adv,+neg] ; // 0:1 2:1
%mod_neg_2 :: you [pos=md,+aux,+neg,sb=[+expl,+p2]]  [pos=adv,+neg] ; // 0:1 2:1
%mod_neg_3sm :: he [pos=md,+aux,+neg,sb=[+expl,-p1,-p2,-plr,-fem]] [pos=adv,+neg] ; // 0:1 2:1
%mod_neg_3sf :: she [pos=md,+aux,+neg,sb=[+expl,-p1,-p2,-plr,+fem]] [pos=adv,+neg] ; // 0:1 2:1
%mod_neg_1p :: we [pos=md,+aux,+neg,sb=[+expl,+p1,+plr]] [pos=adv,+neg] ; // 0:1 2:1
%mod_neg_3p :: they [pos=md,+aux,+neg,sb=[+expl,-p1,-p2,+plr]] [pos=adv,+neg] ; // 0:1 2:1
# default modal subject is 3s
%mod_neg :: [pos=md,+aux,+neg,sb=[+expl,-p1,-p2,-plr]] [pos=adv,+neg] ; // 1:0

## jussive (this has to follow the above because of "he will/can/ought to... let me go")
%v_1ps_jus :: let me [pos=v,tam=stm,sb=[+expl,+p1,-plr],tm=j_i] ; // 0:2 1:2

