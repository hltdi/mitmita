## copula (suffix in Ch)
cop1s :: [pos=n] [pos=cop,tm=prs,sb=[+p1,-plr]] ; 0 -> [cp=1,cn=1,tns=prs] ; // 1:0
cop1p :: [pos=n] [pos=cop,tm=prs,sb=[+p1,+plr]] ; 0 -> [cp=1,cn=2,tns=prs] ; // 1:0
cop2sm :: [pos=n] [pos=cop,tm=prs,sb=[+p2,-fem,-plr]] ; 0 -> [cp=2,cn=1,cg=m,tns=prs] ; // 1:0
cop2sf :: [pos=n] [pos=cop,tm=prs,sb=[+p2,+fem,-plr]] ; 0 -> [cp=2,cn=1,cg=f,tns=prs] ; // 1:0
cop2p  :: [pos=n] [pos=cop,tm=prs,sb=[+p2,+plr]] ; 0 -> [cp=2,cn=2,tns=prs] ; // 1:0
cop3sm :: [pos=n] [pos=cop,tm=prs,sb=[-p1,-p2,-plr,-fem]] ; // 1:0 ; 0 -> [cp=3,cn=1,cg=m,tns=prs]
cop3sf :: [pos=n] [pos=cop,tm=prs,sb=[-p1,-p2,-plr,+fem]] ; // 1:0 ; 0 -> [cp=3,cn=1,cg=f,tns=prs]
cop3sm :: [pos=n] [pos=cop,tm=prs,sb=[-p1,-p2,-plr,-fem]] ; // 1:0 ; 0 -> [cp=3,cn=1,cg=m,tns=prs]
cop3p  :: [pos=n] [pos=cop,tm=prs,sb=[-p1,-p2,+plr]] ; // 1:0 ; 0 -> [cp=3,cn=2,tns=prs]
