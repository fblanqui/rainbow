/TTT2Cert/{ttt++;if($3=="ACCEPT")tttceta++;if($5=="ACCEPT")tttcime++;if($7=="ACCEPT")tttcolor++}
/AProVE-COLOR/{aprovecolor++;if($3=="ACCEPT")aprovecolorceta++;if($5=="ACCEPT")aprovecolorcime++;if($7=="ACCEPT")aprovecolorcolor++}
/AProVE-CeTA/{aproveceta++;if($3=="ACCEPT")aprovecetaceta++;if($5=="ACCEPT")aprovecetacime++;if($7=="ACCEPT")aprovecetacolor++}
/AProVE-A3PAT/{aprovecime++;if($3=="ACCEPT")aprovecimeceta++;if($5=="ACCEPT")aprovecimecime++;if($7=="ACCEPT")aprovecimecolor++}
/cime3finder/{cime++;if($3=="ACCEPT")cimeceta++;if($5=="ACCEPT")cimecime++;if($7=="ACCEPT")cimecolor++}
END{printf "TRS\t\tCertifiers\n\
Provers\t\tProofs\tCeTA\tRainbow\tCime3\n\
TTT2Cert\t%d\t%d\t%d\t%d\n\
AProVE-CeTA\t%d\t%d\t%d\t%d\n\
AProVE-COLOR\t%d\t%d\t%d\t%d\n\
AProve-A3PAT\t%d\t%d\t%d\t%d\n\
Cime3finder\t%d\t%d\t%d\t%d\n\
TOTAL\t\t%d\t%d\t%d\t%d\n",
ttt, tttceta, tttcolor, tttcime,
aproveceta, aprovecetaceta, aprovecetacolor, aprovecetacime,
aprovecolor, aprovecolorceta, aprovecolorcolor, aprovecolorcime,
aprovecime, aprovecimeceta, aprovecimecolor, aprovecimecime,
cime, cimeceta, cimecolor, cimecime,
    ttt+aproveceta+aprovecolor+aprovecime+cime,
    tttceta+aprovecetaceta+aprovecolorceta+aprovecimeceta+cimeceta,
    tttcolor+aprovecetacolor+aprovecolorcolor+aprovecimecolor+cimecolor,
    tttcime+aprovecetacime+aprovecolorcime+aprovecimecime+cimecime}
