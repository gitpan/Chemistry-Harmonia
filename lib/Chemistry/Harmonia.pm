package Chemistry::Harmonia;

use 5.008008;
use strict;
use warnings;

use Carp;
use Chemistry::File::Formula;
use Algorithm::Combinatorics qw( variations_with_repetition subsets );
#use Math::BigInt qw( blcm bgcd );
#use Math::BigRat;
#use Math::Fraction::Egyptian ( );
#use Math::Assistant qw(:algebra);
use Inline::Files;

require Exporter;

our @ISA = qw(Exporter);

our %EXPORT_TAGS = ( 'all' => [ qw(
			parse_chem_mix
			oxidation_state
			) ],
		    'redox' => [ qw(
			parse_chem_mix
			oxidation_state
			) ],
);

our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );

our @EXPORT = qw( );

our $VERSION = '0.05';

use base qw(Exporter);

# Decomposes the chemical equation into 
# arrays of initial substances and products
sub parse_chem_mix{
    $_ = shift; # List of substances with delimiters (spaces, comma, + )
    my $coef = shift; # hash of coefficients
    s/^\s+//;
    s/\s+$//;

    my $m = qr/\s*[ ,+]\s*/;

    # The chemical equation is set: A + B --> C + D
    if( /(.+?)\s*[=-]+>?\s*(.+)/ ){
	my $chem_eq = [ map [ split "$m" ], ($1,$2) ];

	for my $ip ( @$chem_eq ){

	    my @ip_del; # For removal from an array of coefficients

	    for(my $i=0; $i<=$#{ $ip }; $i++ ){
		$_ = $ip->[$i];

		if( /^(\d+)([A-Z].*)/ ){ # together coefficient and substance
		    $coef->{$2} = $1;	# coefficient
		    $ip->[$i] = $2;	# substance

		}elsif( /^(\d+)$/ ){
		    $coef->{ $ip->[$i+1] } = $1; # coefficient
		    push @ip_del, $i;
		}
	    }
	    splice @$ip, $_, 1 for( reverse @ip_del );
	}
	return $chem_eq;
    }

    # list of substances (without '=' or '-'). Last - product
    return [ map [ split "$m" ], ( /(.+)$m(\S+)/ ) ];
}


# Calculation of oxidation state
sub oxidation_state{
    my $chem_sub = shift;

    my $prop;	# Result:
	# HASH{element}{num}[0 .. n-1] - Element amount on everyone 1..n atom
	# HASH{element}{OS}[0 .. n-1][ .. ] - Oxidation States of Element (OSE) arrays 1..n atom 

    # Atomic composition of substance
    my %f = Chemistry::File::Formula->parse_formula($chem_sub);
    return undef unless keys %f;

    my %atoms;	# Hash all atoms

    for my $e (keys %f){
	$prop->{$e}{'num'}[0] = $f{$e}; # Total quantity of atoms for element
	$atoms{$e} = 0;
    }

    my %ions; # Ions: { element }{ ion-pattern }[ array OSE ]

    &_read_ions($chem_sub, \%ions);

    my %atom_el_neg; # atom electronegativity
    my %atom_OS; # oxidation state
    my $intermet = 1; #  for intermetallic compound

    # Read Pauling electronegativity and OSE
    &_read_atoms(\%atoms, \%atom_el_neg, \%atom_OS, \$intermet);

    # Sort atoms in decreasing order of electronegativity.
    # In the beginning - the most electronegative
    my @neg = sort { $atom_el_neg{$b} <=> $atom_el_neg{$a} } keys %atom_el_neg;

    my $balance = 0;	# Electronic balance
    my $max_n_OS = 0;	# Number of OSE in maximum list
    my @atoms;		# Varied atoms of elements

    # List of atoms on decrease of electronegativities
    for(my $i=0; $i <= $#neg; $i++){
	my $e = $neg[$i];	# element

	# By default in the list of OSE only 0th charge
	$prop->{$e}{'OS'}[0] = [ 0 ];

	if($intermet){ # Substance is intermetallic compound
	    $prop->{$e}{'OS'}[1] = [ 0 ]; # 0th charge
	    next;
	}

	# Basic list of OSE
	if( $i == 0 ) { # 1th (most electronegative) -> only '-' OSE

	    # Simple substance - one element
	    if( scalar( keys %{ $prop } ) == 1 ) {
		$prop->{$e}{'OS'}[1] = [ 0 ]; # 0th charge
		last;

	    # Electronegative is identical with next element
	    }elsif( $atom_el_neg{$e} == $atom_el_neg{ $neg[$i+1] }){
		$prop->{$e}{'OS'}[0] = [ grep $_, @{ $atom_OS{$e} } ];

	    }else{
		$prop->{$e}{'OS'}[0] = [ grep $_ < 0, @{ $atom_OS{$e} } ];
	    }

	}elsif( $i == 1 ) { # 2th -> also '-' OSE
	    $prop->{$e}{'OS'}[0] = [ grep $_, @{ $atom_OS{$e} } ];

	}else{	# Others -> only '+' OSE
	    $prop->{$e}{'OS'}[0] = [ grep $_ > 0, @{ $atom_OS{$e} } ];
	}

	# Inert elements
	$prop->{$e}{'OS'}[0] = [ @{ $atom_OS{$e} } ] if $e=~/He|Ne|Ar|Kr|Xe|Rn/;

	my $n = $prop->{$e}{'num'}[0]; # Total quantity of atoms

	# Number of various atoms for element in substance
	my $m = length($e)==1 ? "$e\\d+|$e(?![a-gik-pr-u])" : "$e\\d*";

	for(my $j = 1; $j <= $n; $j++){
	    my $count = 0;

	    # Remove only current atom of element
	    $_ = $chem_sub;
	    s{
	        ($m)
	    }{
	        $1 if ++$count != $j;
	    }gex;
	    last if $_ eq $chem_sub; # Subs isn't (atoms have ended)

	    my %f = Chemistry::File::Formula->parse_formula($_);

	    if( exists $f{$e} ){
		push @{ $prop->{$e}{'num'} }, $n - $f{$e};

	    }else{ # One atom of element in substance
	        push @{ $prop->{$e}{'num'} }, $n;
	    }

	    # Search ion-group. Remove all atoms of element, except current
	    $count = 0;
	    $_ = $chem_sub;
	    s{
	        ($m)
	    }{
		if( ++$count == $j){
		    $1;
		}else{
		    '-';
		}
	    }gex;

	    my $f_os = 1; # is no ion-group

	    # Sort by decrease of ion-group length
	    for my $l (sort {$b <=> $a} keys %{ $ions{$e} } ) {

		for my $mg ( keys %{ $ions{$e}{$l} } ){
		    next unless /$mg/; # Ion-group isn't found

		    # Ion-group is found. Save list of OSE
		    # for j-th atom of element
		    push @{ $prop->{$e}{'OS'} }, $ions{$e}{$l}{$mg};

		    $f_os = 0;
		    last;
		}
		last unless $f_os; # Ion-group is found
	    }

	    if( $f_os ){ # Ion-group isn't found

		# Quantity of OSE from basic list
		my $n_OS = $#{ $prop->{$e}{'OS'}[0] };
		$max_n_OS = $n_OS if $n_OS > $max_n_OS; # max list of OSE

		if( $n_OS ) { # number of OSE > 1
		    # Add in array varied OSE for j-th atom of element
    		    push @atoms,"$e$j";	

		    # Define from a basic list of OSE
	    	    push @{ $prop->{$e}{'OS'} }, [ -999 ];

		}else{ # One OSE in list
		    my $os = $prop->{$e}{'OS'}[0]->[0]; # !!!
		    push @{ $prop->{$e}{'OS'} }, [ $os ];

		    # charge * number of atoms
		    $balance += $os * $prop->{$e}{'num'}[$j];
		}

	    }else{ # Ion-group is found.
		# Calculation total and mean OSE
		my $os;
		$os += $_ for @{ $prop->{$e}{'OS'}[$j] };

		$balance += $os * $prop->{$e}{'num'}[$j] / scalar( @{ $prop->{$e}{'OS'}[$j] } );
	    }
	}
    }

    # Select oxidation states
    if($max_n_OS){
	my $iter = variations_with_repetition( [ (0..$max_n_OS) ], scalar( @atoms ) );
SO_M2:
	while (my $p = $iter->next) {

	    my $bb = 0;
	    for(my $i = 0; $i<=$#{ $p }; $i++){

		my $j = 1;
		my $e = $atoms[$i];
		if($e =~ /(\D+)(\d*)/){
		    $e = $1;
		    $j = $2;
		}
		my $os = $prop->{ $e }{'OS'}[0]->[ $p->[$i] ];	# !!!
		next SO_M2 unless defined $os; # OSE have ended

		$bb += $os * $prop->{ $e }{'num'}[$j];
	    }

	    unless($balance + $bb){ # balance is found
		for(my $i = 0; $i <= $#{ $p }; $i++){

		    my $j = 1;
		    my $e = $atoms[$i];
		    if($e =~ /(\D+)(\d*)/){
			$e = $1;
			$j = $2;
		    }
		    my $os = $prop->{ $e }{'OS'}[0]->[ $p->[$i] ]; # !!!
		    $prop->{ $e }{'OS'}[$j] = [ $os ]
		}
		last;
	    }
	}
    }

    $balance = 0; # for electronic balance

    for my $e (keys % { $prop }){
	# delete starting values 'OS' and 'num'
	shift @{ $prop->{$e}{'OS'} };
	shift @{ $prop->{$e}{'num'} } if $#{ $prop->{$e}{'num'} } > 0; # is more 1

	# Check electronic balance
	for(my $i=0; $i<=$#{ $prop->{$e}{'OS'} }; $i++ ){

	    my($sum, $n);
	    for( @{ $prop->{$e}{'OS'}[$i] } ){
		$sum += $_;
		$n++;
	    }
	    # sum OSE * number of atoms / number of OSE
	    $balance += $sum * $prop->{$e}{'num'}[$i] / $n;
	}
    }

    return $balance ? undef : $prop;
}

# Read Pauling electronegativity and OSE
# only for given element of substance
# input:
#	%atoms - elements
# return:
#	%atom_el_neg
#	%atom_OS
#	$intermet

sub _read_atoms{
    my ($atoms, $atom_el_neg, $atom_OS, $intermet) = @_;

    open PERIODIC;
    while(<PERIODIC>){
	s/\s*#.*//g;		# Delete comments
	next if /^\s*$/;	# To discard blank lines
	chomp;
	my ($e, $neg, $metal, $os) = split /\s+/;

	next if !defined $e || !exists $atoms->{ $e };

	$atom_el_neg->{ $e } = $neg;
	$atom_OS->{ $e } = [ split ';',$os ];
	$$intermet = 0 unless $metal;	# Not intermetallic compound
    }
    close PERIODIC;
}

# Read necessary ion-group
# input:
#	$Chemistry_substance
# return:
#	$ions
sub _read_ions {
    my ($chem_sub, $ions) = @_;

    open IONS;
    while(<IONS>){ # Construct pattern
	chomp;
	s/\s*#.*//g;
	next if /^\s*$/;

	my ($frm, $os) = split /\s+/; # formula (mask) and list of OSE
	
	if($os =~ /~/){ # Macro-substitutions
	    my %a = split /_|=/,$os; # Parse them to element end OSE
	    my %ek;
	    my $max_n_ek = 0; # max number of element-pattern in macro-substitutions

	    for my $k (keys %a){
		if($k =~ /(\w+~)(.*)/){
		    $ek{$1}[0] = [ split ',',$2 ];
		    $ek{$1}[1] = $a{$k}; # OSE for group

		    my $n_ek = $#{ $ek{$1}[0] }; # number of element-substitutions
		    $max_n_ek = $n_ek if $n_ek > $max_n_ek; # max list
		}
	    }
	    
	    my $iter = variations_with_repetition( [ (0..$max_n_ek) ], scalar( keys %ek ) );
ELEMENT_MACRO_1:
	    while (my $p = $iter->next) {
		my $m = $frm; # macro-formula (mask)
		my $i = 0;
		for my $em (sort keys %ek){
		    my $e = $ek{ $em }[0][ $p->[$i++] ];	# element
		    next ELEMENT_MACRO_1 unless defined $e; # pattern have ended

		    $m =~ s/$em/$e/g; # Construct the formula (mask)
		}

		next unless $chem_sub =~ /($m)/; # Ions in substance aren't present

		my $l = length($1); # Length of the found group

		$i = 0;
		for my $em (sort keys %ek){
		    my $e = $ek{ $em }[0][ $p->[$i++] ]; # element
		    $ions->{ $e }{ $l }{ $m } = [ split /;/,$ek{ $em }[1] ]; # list OSE
		}
		
		while(my ($e, $v) = each %a ){
		    $ions->{ $e }{ $l }{ $m } = [ split /;/,$v ] if $e !~ /~/; # list OSE
		}
	    }

	}else{
	    next unless $chem_sub =~ /($frm)/; # no ions in substance

	    my $l = length($1); # Length of the found group

	    my %a = split /_|=/,$os; # decompose on elements
	    while(my ($e, $v) = each %a ){
		$ions->{ $e }{ $l }{ $frm } = [ split /;/,$v ]; # list OSE
	    }
	}
    }
    close IONS;
}


# Pauling scale (adapted)
__PERIODIC__
Ac	110	1	0;3
Ag	193	1	0;1;2;3;5
Al	161	1	-3;0;1;2;3
Am	113	1	0;2;3;4;5;6
Ar	0	0	0
As	221	0	-3;0;3;5	# 2
At	220	0	-1;0;1;5;7	# 3
Au	254	1	0;1;2;3;5;7	# -1
B	204	0	-3;0;1;2;3
Ba	89	1	0;2
Be	157	1	0;2
Bh	0	1	0;7
Bi	221	0	-3;0;2;3;5
Bk	130	1	0;3;4
Br	296	0	-1;0;1;3;5;7	# 4
C	255	0	-4;-1;0;2;3;4	# -3;-2;1
Ca	100	1	0;2
Cd	169	1	0;2
Ce	112	1	0;3;4	# 2
Cf	130	1	0;2;3;4
Cl	316	0	-1;0;1;3;4;5;6;7	# 2
Cm	128	1	0;3;4
Co	188	1	0;1;2;3;4	# -1; 5
Cr	166	1	0;1;2;3;4;5;6	# -2;-1
Cs	79	1	0;1
Cu	190	1	0;1;2;3	# 4
Db	0	1	0;5
Dy	122	1	0;3;4	# 2
Er	124	1	0;3
Es	130	1	0;2;3
Eu	120	1	0;2;3
F	400	0	-1;0
Fe	183	1	0;2;3;4;6;8	# -2;-1; 1; 5
Fm	130	1	0;2;3
Fr	70	1	0;1
Ga	181	1	0;1;2;3
Gd	120	1	0;3	# 1; 2
Ge	201	0	-4;-2;0;2;4	# 1; 3
H	220	0	-1;0;1
He	0	0	0
Hf	130	1	0;2;3;4
Hg	200	1	0;1;2	# 4
Ho	123	1	0;3
Hs	0	1	0;7
I	266	0	-1;0;1;3;5;7
In	178	1	0;1;2;3
Ir	220	1	0;1;2;3;4;5;6;8	# -3;-1
K	82	1	0;1
Kr	0	0	0;2;4;6
Ku	0	1	0
La	110	1	0;3	# 2
Li	98	1	0;1
Lr	129	1	0;3
Lu	127	1	0;3
Md	130	1	0;2;3
Mg	131	1	0;2
Mn	155	1	0;1;2;3;4;5;6;7	# -3;-2;-1
Mo	216	1	0;2;3;4;5;6	# -2;-1; 1
Mt	0	1	0;4
N	304	0	-3;-2;-1;0;1;2;3;4;5
Na	93	1	0;1
Nb	160	1	0;1;2;3;4;5	# -1
Nd	114	1	0;3	# 2
Ne	0	0	0
Ni	191	1	0;1;2;3;4	# -1
No	130	1	0;2;3
Np	136	1	0;3;4;5;6	# 7
Ns	0	1	0
O	344	0	-2;-1;0;1;2
Os	220	1	0;2;3;4;5;6;7;8	# -2;-1; 1
P	221	0	-3;-2;0;1;3;4;5	# -1; 2
Pa	150	1	0;3;4;5
Pb	233	1	-4;0;2;4
Pd	220	1	0;1;2;3;4
Pm	113	1	0;3
Po	200	1	-2;0;2;4;6
Pr	113	1	0;3;4	# 2
Pt	228	1	0;1;2;3;4;5;6
Pu	128	1	0;2;3;4;5;6	# 7
Ra	90	1	0;2;4
Rb	82	1	0;1
Re	190	1	0;1;2;3;4;5;6;7	# -3;-1
Rf	0	1	0;4
Rh	228	1	0;1;2;3;4;6	# -1; 5
Rn	0	0	0;2;4;6;8
Ru	220	1	0;2;3;4;5;6;7;8	# -2; 1
S	258	0	-2;0;1;2;3;4;6	#-1; 5
Sb	221	1	-3;0;3;4;5
Sc	136	1	0;3		# 1; 2
Se	255	0	-2;0;2;4;6	
Sg	0	1	0;6
Si	190	0	-4;0;2;4	# -3;-2;-1; 1; 3
Sm	117	1	0;2;3
Sn	196	1	-4;-2;0;2;4
Sr	95	1	0;2
Ta	150	1	0;1;2;3;4;5	# -1
Tb	110	1	0;3;4	# 1
Tc	190	1	0;1;2;3;4;5;6;7	# -3;-1
Te	221	0	-2;0;2;4;6	# 5
Th	130	1	0;2;3;4
Ti	154	1	-2;0;2;3;4	# -1
Tl	162	1	0;1;3
Tm	125	1	0;2;3
U	138	1	0;3;4;5;6
V	163	1	0;2;3;4;5	# -1; 1
W	220	1	0;2;3;4;5;6	# -2;-1; 1
Xe	0	0	0;1;2;4;6;8
Y	122	1	0;3	# 1; 2
Yb	110	1	0;2;3
Zn	165	1	0;2
Zr	133	1	0;2;3;4	# 1

__IONS__
# hydroxide
[^O]OH(?![efgos])	H=1_O=-2
# nitrites, meta- antimonites, arsenites
.a~O2		a~N,Sb,As=3_O=-2
# carbonates, celenates, tellurates
.a~O3		a~C,Se,Te=4_O=-2
# bismuthates, nitrates, meta-phosphates and others
.a~O3		a~Bi,N,P,Cl,Br,I=5_O=-2
# ortho- antimonates, arsenates, phosphates and others
.a~O4		a~Sb,As,P,V=5_O=-2
# molybdates, tungstates, chromates and others (excepting peroxides)
.a~O4(?=[^O]|Os|$)	a~Kr,U,S,Se,Te,Re,Mo,W,Cr=6_O=-2
# per- chlorates, bromates, iodates
.a~O4		a~Cl,Br,I=7_O=-2
# plumbates, silicates
.a~O4		a~Pb,Si=4_O=-2	
# rhodanides (thiocyanates) and for selenium
.(?:a~CN|a~NC|CNa~|Ca~N|Na~C|NCa~)(?![a-gik-pr-u])	a~S,Se=-2_C=4_N=-3
# per-carbonates (percarbonic acid)
.C2O6		C=4_O=-2;-2;-2;-2;-1;-1
# sulphites
.SO3(?=[^OS]|Os|S[bcegimnr]|$)	S=4_O=-2	
# thiosulphates
.S2O3		S=6;-2_O=-2
# pirosulphates
.S2O7		S=6_O=-2

.IO[56]		I=7_O=-2

.BO3		B=3_O=-2
# bichromates
.Cr2O7		Cr=6_O=-2
# rhodane
^\((?:SCN|SNC|CNS|CSN|NSC|NCS)\)2$	S=1_C=2_N=-3
# cyan (dicyan)
^\((?:CN|NC)\)2$	C=4;2_N=-3
# cyanides
.CN		C=2_N=-3
# cyanates (salts of cyanic, isocyanic acid)
.CNO		C=4_N=-3_O=-2
# fulminates (salts of fulminic acid)
.ONC		C=-2_N=3_O=-2
# flaveanic hydrogen
^C2(?:H2N2S|N2SH2|SH2N2|SN2H2)$	C=2;4_H=1_S=-2_N=-3
# rubeanic hydrogen
^C2S2N2H4$	C=2;4_H=1_S=-2_N=-3
# salts of peroxonitric acid
.NO4		N=5_O=-1;-1;-2;-2
# salts of hyponitrous acid
.N2O2		N=1_O=-2
# salts of nitroxylic acid
.N2O4		N=2_O=-2
# salts of hydrazonic acid and azides (pernitrides)
(?:.[\[\(]?N3[\]\)]?|^N3H$)	N=-1;0;0
^(?:a~3\(N2\)2|a~3N4)$	a~Ca=2_N=-2;-2;-2;0	# ?
# diimide
^N2H2$		H=1_N=-2;0
# ammonia
NH[34]		H=1_N=-3	

.BrO		Br=1_O=-2

.BF4		B=3_F=-1

.NH2Br		H=1_N=-3_Br=-1

#.P\d+O\d+	P=5_O=-2	# polyphosphates
#.SbO3		Sb=3/5_O=-2	# ortho-antimonites / meta-antimonates
#.AsO3		As=3/5_O=-2	# ortho-arsenites / meta-arsenates
#.TcO4		Tc=6/7_O=-2
#.RuO4		Ru=6/7_O=-2

# Neutral ligands
CO\(NH2\)2		C=4_H=1_N=-3_O=-2
H2O(?=[^2O]|Os|$)	H=1_O=-2
# metal ammiakaty
^a~\(NH3\)\d*$		a~Ca=0_H=1_N=-3

^(?:HOF|HFO|OFH|FOH)$	H=1_F=1_O=-2
^Bi2O4$		Bi=3;5_O=-2
^B4H10$		B=2;2;3;3_H=-1
^Fe3C$		Fe=2;2;0_C=-4
^Fe3P$		Fe=3;0;0_P=-3
^P4S3$		P=1_S=-2;-2;0
^P4S7$		P=1_S=-2;-2;0;0;0;0;0
^P4S10$		P=1_S=-2;-2;0;0;0;0;0;0;0;0
^P12H6$		H=1_P=-3;-3;0;0;0;0;0;0;0;0;0;0
# compound oxide
^Pb3O4$		Pb=2;2;4_O=-2
^a~3O4$		a~Fe,Co=2;3;3_O=-2
# carbonyls
^a~\d*\(CO\)\d*$	a~V,W,Cr,Ir,Mn,Fe,Co,Ni,Mo,Tc,Re,Ru,Rh,Os=0_C=2_O=-2
# alkaline metals and others
^a~2O2			a~H,Li,Na,K,Rb,Cs,Fr,Hg=1_O=-1	# peroxides
^(?:a~O2|a~2O4)		a~Li,Na,K,Rb,Cs,Fr=1_O=-1;0	# superoxides
^a~O3			a~Li,Na,K,Rb,Cs,Fr=1_O=-1;0;0	# ozonide
# alkaline-earth metals and others
^a~O2			a~Mg,Ca,Sr,Ba,Ra,Zn,Cd,Hg,Cu=2_O=-1	# peroxides
^(?:a~\(O2\)2|a~O4)	a~Mg,Ca,Sr,Ba,Ra=2_O=-1;0	# superoxides
^(?:a~\(O2\)3|a~O6)	a~Mg,Ca,Sr,Ba,Ra=2_O=-1;0;0	# ozonide
# all peroxides
.\(O2\)			O=-1
# dioxygenils (except O2F2)
^(?:\(O2\)|O2)(?![F])	O=1;0
# chromium peroxide
^CrO5$		Cr=6_O=-2;-1;-1;-1;-1
# platinum hexafluoride (strongest oxidizer)
.PtF[6-9]$		Pt=5_F=-1
__IONS_END__

1;
__END__

=head1 NAME

Chemistry::Harmonia - Decision of simple and difficult chemical puzzles.

=head1 SYNOPSIS

  use Chemistry::Harmonia qw(:redox);
  use Data::Dumper;

  for my $formula ('Fe3O4', '[Cr(CO(NH2)2)6]4[Cr(CN)6]3'){
    my $ose = oxidation_state( $formula );
    print Dumper $ose;
  }

  my $chemical_equation = 'KMnO4 + NH3 --> N2 + MnO2 + KOH + H2O';
  print Dumper parse_chem_mix( $chemical_equation );

Will print something like:

  $VAR1 = {
          'O' => {
                  'num' => [ 4 ],
                  'OS' => [ [ -2 ] ]
                 },
          'Fe' => {
                  'num' => [ 3 ],
                  'OS' => [ [ 2, 3, 3 ] ]
                 }
         };
  $VAR1 = {
          'H' => { 'num' => [ 96 ],
                   'OS' => [ [ 1 ] ]
                 },
          'O' => { 'num' => [ 24 ],
                   'OS' => [ [ -2 ] ]
                 },
          'N' => { 'num' => [ 48, 18 ],
                   'OS' => [ [ -3 ], [ -3 ] ]
                 },
          'C' => { 'num' => [ 24, 18 ],
                   'OS' => [ [ 4 ], [ 2 ] ]
                 },
          'Cr' => { 'num' => [ 4, 3 ],
                    'OS' => [ [ 3 ], [ 2 ] ]
                  }
        };
  $VAR1 = [
	    ['KMnO4', 'NH3'],
	    ['N2', 'MnO2', 'KOH','H2O']
	];


=head1 DESCRIPTION

The module provides the necessary subroutines to solve some puzzles of the
general inorganic chemistry. The methods implemented in this module, are all
oriented to known rules and laws of general chemistry.

=head1 SUBROUTINES

Chemistry::Harmonia provides these subroutines:

    oxidation_state( $formula_of_substance )
    parse_chem_mix( $mix_of_substances [, \%coefficients ] )

All of them are context-sensitive.


=head2 oxidation_state( $formula_of_substance )

This subroutine returns the hash reference of hash integer oxidation state (key
'OS') and hash with the number of atoms for each element (key 'num') for the
inorganic C<$formula_of_substance>.

Always use the upper case for the first character in the element name
and the lower case for the second character from Periodic Table. Examples: Na,
Ag, Co, Ba, C, O, N, F, etc. Compare: Co - cobalt and CO - carbon monoxide.

For very difficult mysterious formula (usually organic) returns C<undef>.


=head2 parse_chem_mix( $mix_of_substances [, \%coefficients ] )

This subroutine parses C<$mix_of_substances> (usually chemical equation)
into arrays of the initial substances and products.
A chemical equation consists of the chemical formulas of the reactants (the
starting substances) and the chemical formula of the products (substances formed
in the chemical reaction).

Separator of the reactants from products can be sequence '=', '-' and single
'>'. For example: =, ==, =>, ==>, -, --, ->, -->, etc.
Spaces round a separator are not essential.
If the separator is not set, last substance of a mix will be a product only.

Each individual substance's chemical formula is separated from others by a plus
sign ('+'), comma and/or space.
Valid examples:

  print Dumper parse_chem_mix( 'KNO3 + S K2SO4 , NO SO2' );

Will print something like:

  $VAR1 = [
            [ 'KNO3','S','K2SO4','NO' ],
            [ 'SO2' ]
        ];

If in C<$mix_of_substances> is stoichiometric coefficients they collect in hash
reference C<\%coefficients>. Attention: the reactants and products should be
separated here. Next example:

  my %coef;
  my $chem_eq = 'BaS + 2 H2O = Ba(OH)2 + 1 Ba(SH)2';

  my $out_ce = parse_chem_mix( $chem_eq, \%coef );
  print Dumper( $out_ce, \%coef );

Will print something like:

  $VAR1 = [ [ 'BaS','H2O'],
            [ 'Ba(OH)2', 'Ba(SH)2']
        ];
  $VAR2 = {
          'Ba(SH)2' => '1',
          'H2O' => '2'
        };


=head2 EXPORT

Chemistry::Harmonia exports nothing by default.
Each of the subroutines can be exported on demand, as in

  use Chemistry::Harmonia qw( oxidation_state );

the tag C<redox> exports the subroutines C<oxidation_state>
and C<parse_chem_mix>:

  use Chemistry::Harmonia qw(:redox);

and the tag C<all> exports them all:

  use Chemistry::Harmonia qw(:all);


=head1 DEPENDENCIES

Chemistry::Harmonia is known to run under perl 5.8.8 on Linux.
The distribution uses L<Chemistry::File::Formula>,
L<Algorithm::Combinatorics> and L<Inline::Files>
for the subroutine C<oxidation_state()> and L<Carp>.

=head1 SEE ALSO

Greenwood, Norman N.; Earnshaw, Alan. (1997), Chemistry of the Elements (2nd
ed.), Oxford: Butterworth-Heinemann

Irving Langmuir. The arrangement of electrons in atoms and molecules. J. Am.
Chem. Soc. 1919, 41, 868-934.

L<Chemistry-Elements>, L<Chemistry::Mol>, L<Chemistry::File> and
L<Chemistry::MolecularMass>.


=head1 AUTHOR

Alessandro Gorohovski, E<lt>angel@feht.dgtu.donetsk.uaE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2011 by A. N. Gorohovski

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.8.8 or,
at your option, any later version of Perl 5 you may have available.

=cut
