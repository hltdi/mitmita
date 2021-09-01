# still have to include Amh POSs: n_dv[v=agt], n_dv[v=inf], v[+rel], nn_*
n_cop3sm :: [pos=n,cp=3,cg=m,cn=1,tns=prs] [pos=cop,sb=[-fem,-p1,-p2,-plr]] ; // 1:0
# a_cop3sm :: [pos=adj,cp=3,cg=m,cn=1,tns=prs] [pos=cop,sb=[-fem,-p1,-p2,-plr]] ; // 1:0 ; 0-> [pos=n]
n_cop3sf :: [pos=n,cp=3,cg=f,cn=1,tns=prs] [pos=cop,sb=[+fem,-p1,-p2,-plr]] ; // 1:0
# a_cop3sf :: [pos=adj,cp=3,cg=f,cn=1,tns=prs] [pos=cop,sb=[+fem,-p1,-p2,-plr]] ; // 1:0 ; 0-> [pos=n]
n_cop3p :: [pos=n,cp=3,cn=2,tns=prs] [pos=cop,sb=[-p1,-p2,+plr]] ; // 1:0
a_cop3p :: [pos=adj,cp=3,cn=2,tns=prs] [pos=cop,sb=[-p1,-p2,+plr]] ; // 1:0 ; 0 -> [pos=n]
n_cop1s :: [pos=n,cp=1,cn=1,tns=prs] [pos=cop,sb=[+p1,-p2,-plr]] ; // 1:0
a_cop1s :: [pos=adj,cp=1,cn=1,tns=prs] [pos=cop,sb=[+p1,-p2,-plr]] ; // 1:0 ; 0-> [pos=n]
n_cop1p :: [pos=n,cp=1,cn=2,tns=prs] [pos=cop,sb=[+p1,-p2,+plr]] ; // 1:0
a_cop1p :: [pos=adj,cp=1,cn=2,tns=prs] [pos=cop,sb=[+p1,-p2,+plr]] ; // 1:0 ; 0-> [pos=n]
n_cop2sm :: [pos=n,cp=2,cn=1,cg=m,tns=prs] [pos=cop,sb=[-p1,+p2,-fem,-plr]] ; // 1:0
a_cop2sm :: [pos=adj,cp=2,cn=1,cg=m,tns=prs] [pos=cop,sb=[-p1,+p2,-fem,-plr]] ; // 1:0 ; 0-> [pos=n]
n_cop2sf :: [pos=n,cp=2,cn=1,cg=f,tns=prs] [pos=cop,sb=[-p1,+p2,+fem,-plr]] ; // 1:0
a_cop2sf :: [pos=adj,cp=2,cn=1,cg=f,tns=prs] [pos=cop,sb=[-p1,+p2,+fem,-plr]] ; // 1:0 ; 0-> [pos=n]
n_cop2p :: [pos=n,cp=2,cn=1,tns=prs] [pos=cop,sb=[-p1,+p2,+plr]] ; // 1:0
a_cop2p :: [pos=adj,cp=2,cn=1,tns=prs] [pos=cop,sb=[-p1,+p2,+plr]] ; // 1:0 ; 0-> [pos=n]
