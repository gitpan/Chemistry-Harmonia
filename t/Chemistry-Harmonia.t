use strict;
use warnings;

use Test::More 'no_plan';

BEGIN { use_ok('Chemistry::Harmonia') };
use Chemistry::Harmonia qw(:all);

use Inline::Files;
use Math::BigInt qw( bgcd );


##### Test oxidation_state() #####

open SUBSTANCES;
while(<SUBSTANCES>){
    chomp;
    s/\s*#.*//g;
    next if /^\s*$/;

    my ($chem_sub, $sample) = split /\s+/; # mask and list OSE

    my %ion_test;
    for my $a ( split /_/,$sample ){ # parse elements
	my ($e, $v) = split /=/,$a;
	my($sum, $n);
	for(split /;/,$v){
	    $sum += $_;
	    $n++;	# quantity
	}
	my $gcd = bgcd(abs($sum), $n);
	if($gcd > 1){
	    $sum /= $gcd;
	    $n /= $gcd;
	}
	push @{ $ion_test{$e} }, $n > 1 ? "$sum/$n" : $sum; # array OSE
    }
    
    # Analyzed substances
    my $ions = oxidation_state($chem_sub);

    for my $e ( keys %{ $ions } ){ # Element
	for( @{ $ions->{$e}{'OS'} } ) {
	    my($sum, $n);
	    for( @{ $_ } ){
		$sum += $_;
		$n++;	# quantity
	    }
	    my $gcd = bgcd(abs($sum), $n);
	    if($gcd > 1){
		$sum /= $gcd;
		$n /= $gcd;
	    }
	    my $ion = $n > 1 ? "$sum/$n" : $sum;

	    is($ion, shift( @{ $ion_test{$e} } ), "element '$e'");
	}
    }
}

exit;

# BD for test oxidation_state()
__SUBSTANCES__
NaSeCN		Na=1_Se=-2_C=4_N=-3
HOF		H=1_F=1_O=-2
Mg2Ge		Mg=2_Ge=-4
MnAs		Mn=3_As=-3
GaAs		Ga=3_As=-3
XeFPtF6		Xe=2_Pt=5_F=-1_F=-1
XePtF6		Xe=1_Pt=5_F=-1
O2PtF6		O=1;0_Pt=5_F=-1
O2BF4		O=1;0_B=3_F=-1
Na5P3O10	Na=1_P=5_O=-2
Ca(NH3)6	Ca=0_H=1_N=-3
Ca3N4		Ca=2_N=-3;-3;0;0
BPO4		B=3_P=5_O=-2
Na3[Ti(O2)F5]	Na=1_Ti=4_O=-1_F=-1
K3[Nb(O2)4]	K=1_Nb=5_O=-1
NH4OOH		N=-3_H=1_H=1_O=-1_O=-1
(NH4)2O2	N=-3_H=1_O=-1
MnSO4		Mn=2_S=6_O=-2
AlH3		Al=3_H=-1
B4C		B=1_C=-4
Na4N2O4		Na=1_N=2_O=-2
Bi2O4		Bi=3;5_O=-2
Na2N2O2		Na=1_N=1_O=-2
(NH4)3BiS4	H=1_Bi=5_S=-2_N=-3
BiH3		H=1_Bi=-3
SbH3		H=1_Sb=-3
AsH3		H=1_As=-3
# C2H2N2S2Pb	C=3_H=1_N=-3_S=-2_Pb=2
S(CN)2		S=2_C=2_N=-3
HeH2O		He=0_H=1_O=-2
NaCSN		Na=1_C=4_S=-2_N=-3
Mg3Bi2		Mg=2_Bi=-3
O2F2		O=1_F=-1
C2N2		C=3_N=-3
[Mn(N3)4]OH	Mn=5_H=1_O=-2_N=-1;0;0
K2Cd(N3)4	K=1_Cd=2_N=-1;0;0
NCl3		N=3_Cl=-1
TeH2		H=1_Te=-2
WTe2		W=4_Te=-2
BP		B=3_P=-3
B2H6		B=3_H=-1
BaKrO4		Ba=2_Kr=6_O=-2
AcOBr		Ac=3_O=-2_Br=-1
H2Se		H=1_Se=-2
AsH3		H=1_As=-3
AgO		Ag=2_O=-2
Cu2O3		Cu=3_O=-2
Fe3C		Fe=2;2;0_C=-4
Fe3P		Fe=3;0;0_P=-3
P4S3		P=1_S=-2;-2;0
P4S7		P=1_S=-2;-2;0;0;0;0;0
P4S10		P=1_S=-2;-2;0;0;0;0;0;0;0;0
P12H6		H=1_P=-3;-3;0;0;0;0;0;0;0;0;0;0
H4P2O5		H=1_P=3_O=-2
PH3		P=-3_H=1
P2H4		P=-2_H=1
HN3		H=1_N=-1;0;0
HNO4		H=1_N=5_O=-1;-1;-2;-2
K4[Fe(CN)6]	K=1_Fe=2_C=2_N=-3
K2FeO4		K=1_Fe=6_O=-2
VOCl3		V=5_Cl=-1_O=-2
V2O3		V=3_O=-2
VI2		V=2_I=-1
TiH4		Ti=4_H=-1
Ti2S3		Ti=3_S=-2
Sc(NO3)3	Sc=3_N=5_O=-2
Cl2O		Cl=1_O=-2
S2O		S=1_O=-2
P4O10		P=5_O=-2
H4P2O6		H=1_P=4_O=-2
P4O6		P=3_O=-2
H3PO2		H=1_P=1_O=-2
[Cr(CO(NH2)2)6]4[Cr(CN)6]3	Cr=3_Cr=2_C=4_C=2_H=1_N=-3_N=-3_O=-2
[W6Cl8]Cl4	W=2_Cl=-1_Cl=-1
(CNS)2		C=2_N=-3_S=1
OF2		O=2_F=-1
COCl2		C=4_O=-2_Cl=-1
H2S2O4		H=1_S=3_O=-2
P2H4		H=1_P=-2
NaH		Na=1_H=-1
CrO2Cl2		Cr=6_Cl=-1_O=-2
Na3PO4		Na=1_P=5_O=-2
Na3VO4		Na=1_V=5_O=-2
Na2SO4		Na=1_S=6_O=-2
Na2SeO4		Na=1_Se=6_O=-2
Na2TeO4		Na=1_Te=6_O=-2
Na2ReO4		Na=1_Re=6_O=-2
Na2MoO4		Na=1_Mo=6_O=-2
Na2WO4		Na=1_W=6_O=-2
Na2CrO4		Na=1_Cr=6_O=-2
CrO5		Cr=6_O=-2;-1;-1;-1;-1
Na2CO3		Na=1_C=4_O=-2
Na2SO3		Na=1_S=4_O=-2
Na2SeO3		Na=1_Se=4_O=-2
Na2TeO3		Na=1_Te=4_O=-2
Na2S2O3		Na=1_S=-2;6_O=-2
Na2SO3S		Na=1_S=-2_S=6_O=-2
Na2S2O7		Na=1_S=6_O=-2
Na2Cr2O7	Na=1_Cr=6_O=-2
NaSCN		Na=1_S=-2_C=4_N=-3
NaCNS		Na=1_S=-2_C=4_N=-3
NaNSC		Na=1_S=-2_C=4_N=-3
NaSNC		Na=1_S=-2_C=4_N=-3
NH4NO3		H=1_N=-3_N=5_O=-2
NaClO4		Na=1_Cl=7_O=-2
Na4SiO4		Na=1_Si=4_O=-2
NaBF4		Na=1_B=3_F=-1
NaOH		Na=1_H=1_O=-2
NaCN		Na=1_C=2_N=-3
Na2NH2Br	Na=1_H=1_N=-3_Br=-1
CO(NH2)2	C=4_H=1_N=-3_O=-2
H2O		H=1_O=-2
N2H4		H=1_N=-2
N3H		H=1_N=-1;0;0
NH3		H=1_N=-3
Fe3O4		Fe=2;3;3_O=-2
Pb3O4		Pb=2;2;4_O=-2
LiO2		Li=1_O=0;-1
NaO2		Na=1_O=0;-1
KO2		K=1_O=0;-1
RbO2		Rb=1_O=0;-1
CsO2		Cs=1_O=0;-1
FrO2		Fr=1_O=0;-1
LiO3		Li=1_O=0;0;-1
NaO3		Na=1_O=0;0;-1
KO3		K=1_O=0;0;-1
RbO3		Rb=1_O=0;0;-1
CsO3		Cs=1_O=0;0;-1
FrO3		Fr=1_O=0;0;-1
H2C2O6		H=1_C=4_O=-2;-2;-2;-2;-1;-1
(CN)2		C=3_N=-3
Cr(CO)6		Cr=0_C=2_O=-2
HCNO		H=1_C=4_N=-3_O=-2
HONC		H=1_C=-2_N=3_O=-2
COS		C=4_O=-2_S=-2
N2H4		H=1_N=-2
N2H2		H=1_N=-2;0
CS2		C=4_S=-2
Ba3(MnO4)2Ba2MnO4	Ba=2_Ba=2_Mn=4_Mn=6_O=-2_O=-2
Ba2V2O7		Ba=2_V=5_O=-2
Ba3(MnO4)2	Ba=2_Mn=5_O=-2
Mg6Al2(OH)16CO3	Mg=2_Al=3_O=-2_H=1_C=4_O=-2

__SUBS_END__
