package Chemistry::Harmonia;

use 5.008008;
use strict;
use warnings;

use Carp;
use Chemistry::File::Formula;
use Algorithm::Combinatorics qw( variations_with_repetition subsets );
use String::CRC::Cksum qw( cksum );
use Math::BigInt qw( blcm bgcd );
use Math::BigRat;
use Math::Assistant qw(:algebra);
use Inline::Files;
use Regexp::Common;

require Exporter;

our @ISA = qw(Exporter);

our %EXPORT_TAGS = ( 'all' => [ qw(
			parse_chem_mix
			prepare_mix
			oxidation_state
			class_cir_brutto
			good_formula
			ttc_reaction
			) ],
		    'redox' => [ qw(
			parse_chem_mix
			prepare_mix
			oxidation_state
			) ],
		    'equation' => [ qw(
			parse_chem_mix
			prepare_mix
			class_cir_brutto
			good_formula
			ttc_reaction
			) ],
);

our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );

our @EXPORT = qw( );

our $VERSION = '0.0777';

use base qw(Exporter);


# Returns array of "good" chemical formulas
sub good_formula{
    my $substance = shift || return;
    my $opts = shift;

    for( $substance ){
	s/j/I/ig;	# Replacement by iodine
	1 while s/(?<!\d)0(?![,.]\d)/o/g; # must be oxigen?
    }

    my(@maU, @maUl);
    my %sa;	# Letters of possible atoms

    # Possible atoms of substance
    open PERIODIC;
    while(<PERIODIC>){
	if( /^(\w+)/ ){
	    $_ = $1;
	    if( $substance =~ /$_/i ){
		if( length > 1 ){
		    push @maUl, $_; # Double symbol: 1th - CAPITAL, 2th - small
		}else{
		    push @maU, $_; # Unary symbol
		}
		$sa{ uc $_ } = '' for split //; # String of CAPITAL letters
	    }
	}
    }
    close PERIODIC;

    # All atom letters (CAPITAL)
    my $sas = join('', keys %sa) || return;

    for( $substance ){
	s/,/./g;
	s/[^0-9\.\*\(\)\[\]\{\}$sas]+//ig; # to clean bad symbols
	s/(?<!\d)\.+(?!\d)//g;	# to clean points

	# clean sequences not unary symbols
	while( @maU && $sas =~ /([^@maU])/gx ){
	    my $ul = $1;
	    s/($ul)$ul+($ul)/$1$2/ig;
	}

	# remove bordering brackets
	s/^.|.$//g while /($RE{balanced}{-parens=>'(){}[]'})/g && $_ eq $1;

	# Double symbol similar unary with coefficint
	return [ "\u$_", uc ] if /^@maUl\d+$/i && /^(?i:[@maU])\L[@maU]\d+$/;

	# Normalization of oxide-coated formulas (written through '*')
	if(/\*/){
	    my %k;
	    my $l = 1;
	    for my $i (split /\*/){
		if($i =~ /^(\d+)[a-zA-Z]/){	# Integer coefficient
		    $k{ $1 } = $1;

		}elsif($i =~ /^(\d*\.(\d+))/){ # Fractional coefficient
		    $k{ $1 } = $1;
		    $l *= 10 if length $2 >= length $l;

		}else{	# without coefficient (=1)
		    $k{ '' } = 1;
		}
	    }

	    if( $l > 1 ){
		$k{ $_ } *= $l for keys %k;
	    }
	    # by GCD reduce order of coefficients
	    my $gcd = bgcd(values %k);

	    if( $gcd > 1 ){
		$k{ $_ } /= $gcd for keys %k;
	    }

	    my $f;
	    for my $i (split /\*/){
		$i =~ s/^(\d*\.?\d*)([\w\(\)\[\]\{\}]+)$/$k{$1}>1?"{$2}".$k{$1}:"{$2}"/e;
		$f .= $i;
	    }
	    $_ = $f;
	}

	1 while s/[\(\{\[][\)\}\]]//g;	# clean empty brackets
    }

    my $cf = [''];
    my $mz = '(?<!1)0(?=[^1-9]|$)';	# mask for 'zero2oxi'

    for my $s (split /((?:\d|\(|\)|\[|\]|\{|\})+)/,$substance){

	if( $s =~ /[$sas]/i ){ # Atom symbols
	    &_in_gf($s, \@maU, \@maUl, $cf);
	
	}elsif($s =~ /$mz/ && exists( $opts->{'zero2oxi'} ) ){ # Zero symbols
	    my $z = $s;
	    $s =~ s/$mz/O/g;	# oxigen
	    my $n = $#{$cf};

	    for( my $i = 0; $i <= $n; $i++ ){
		$cf->[$i + $n + 1] = $cf->[$i].$s;	# oxigen
		$cf->[$i] .= $z;	# zero
	    }

	}else{ # Others
	    $_ .= $s for @$cf;
	}
    }

    $cf->[0] =~ /\w/ ? return $cf : return;
}


sub _in_gf{
    my($s, $maU, $maUl, $cf) = @_;

    # Unary symbols of fragment
    my @i_maU = grep $s =~ /$_/i, @$maU;

    if( length($s) == 1 ){	# Unary atom symbol
	@i_maU || return;

	$_ .= $i_maU[0] for @$cf;
	return 1;
    }

    # Double symbols of fragment
    ( my @i_maUl = grep $s =~ /$_/i, @$maUl ) || @i_maU || return; # not present

    # Strings of unary and double atom letters
    my $saU = join '', @i_maU;	# String of unary atom letters
    my $saUl = join '|', @i_maUl; # 1th - CAPITAL, 2th - small

    my @w;	# Anchor symbols

    # Unique unary symbols (is not present in double)
    for( @i_maU ){
	next if $saUl =~ /$_/i;
	$s =~ s/\L$_/$_/g;	# to CAPITAL
	push @w, $_;
    }

    # Unique double (is not present in others)
    for my $ul (@i_maUl){
	(my $m = $saUl) =~ s/$ul//; # To copy and clean the tested

	for(split //,$ul){
	    next if $m =~ /$_/i || $saU =~ /$_/i;

	    $s =~ s/$ul/$ul/ig;
	    push @w, $ul;
	    last;
	}
    }

    $_ = $s;

    if( length == 2){ # Two symbols

	(my $salU = $saUl) =~ s/(\w+)/\l\U$1/g;	# 1th - small, 2th - CAPITAL

	# The order is important!!!
	my @in_cf;
	if( /$saUl/ || /[$saU]{2}/ ){	# Usual writing of atom: 1th - CAPITAL, 2th - small
				# or both - CAPITAL unary letters
	    push @in_cf, $_;

	}elsif( /\U$saUl/ ){ # 1th and 2th - CAPITAL letters of double symbol
	    push @in_cf, ucfirst lc;

	}elsif( @i_maU && ( /[$saU][\L$saU\E]/ || /[\L$saU\E][$saU]/ ) ){ # For unary symbols:
		    # 1th - CAPITAL, 2th - small or 1th - small, 2th - CAPITAL letter
	    push @in_cf, uc;

	}elsif( /$salU/ ){ # 1th - small, 2th - CAPITAL letter of double symbol
	    push @in_cf, ucfirst lc;

	}elsif( length($saUl) == 0 ){ # Without double symbol
	    s/.?([$saU]+).?/$1/i; # unary symbol(s)
	    push @in_cf, uc;

	}else{	# 1th and 2th small letters - two alternative variants
	    if( /[\L$saU]{2}/ ){ # unary symbols
		push @in_cf, uc;
	    }
	    if( /\L$saUl/ ){ # double symbol
		push @in_cf, ucfirst;
	    }

	    @in_cf || return;

	    if( @in_cf == 2 ){

		my $n = $#{$cf};
		for( my $i = 0; $i <= $n; $i++ ){
		    $cf->[$i + $n + 1] = $cf->[$i].$in_cf[1];
		    $cf->[$i] .= $in_cf[0];
		}
		return 1;
	    }
	}

	$_ .= $in_cf[0] for @$cf;
	return 1;
    }

    # More 2 symbols

    for( $s ){
	my $m = join '|', $saUl, @i_maU;

	while( ! /^(?:$m)/i ){ s/^.// } # Clear head
	while( ! /(?:$m)$/i ){ s/.$// } # Clear tail

	# Search double and unary symbols
	my $z = '';
	while( /^((?:$m)+)/g ){ $z .= $1 } 

	if( length $z ){

	    $_ .= $z for @$cf;
	    return 1 if length($z) == length;	# The end

	    s/^$z//;
	    return &_in_gf($_, \@i_maU, \@i_maUl, $cf) if 3 > length;
	}
    }

    if( @w ){	# Search by fragments of anchor symbols 
	my $m = join '|', @w;

	for my $f (split /($m)/, $s){

	    &_in_gf($f, \@i_maU, \@i_maUl, $cf);

	    if( $#{$cf} ){ # For >1 formula
		# To leave the longest fragments
		for( my $i = $#$cf; $i > 0; $i-- ){
		    splice @$cf, $i, 1 if length( $cf->[$i] ) < length( $cf->[0] );
		}
	    }
	}
	return 1;
    }

    # Difficult fragment
    my $cf_copy = [ @$cf ];
    $#{$cf} = -1;	# Reset

_M_gf_1: # Letter by letter search
    for( my $i = 1; $i < length($s); $i++ ){

        my $cf_new = [ @$cf_copy ];

	for( $s =~ /^(\w{$i})(\w+)/ ){
	    &_in_gf($_, \@i_maU, \@i_maUl, $cf_new) || next _M_gf_1;
	}
	# To accumulate only unique, big fragments
	for my $k ( @$cf_new ){
	    scalar( grep length($_) > length($k) || $_ eq $k, @$cf ) || push @$cf, $k;
	}
    }
    return 1;
}


# Tactico-technical characteristics of chemical reaction.
# Return quantity hash (SAR):
#	's'ubstance
#	'a'toms
#	'r'ank
sub ttc_reaction{
    my $ce = shift || return;
    
    # Hash atom matrix and quantity of atoms
    my( $atoms_substance, $atoms ) = &_search_atoms_subs( $ce );

    my $rank = Rank( [ values %$atoms_substance ] ) || return;

    return { 's' => scalar( keys %$atoms_substance ),
	    'a' => $atoms,
	    'r' => $rank,
	    };
}

# Calculation common identifier for reaction:
#	Alphabetic CLASS
# and
#	Chemical Interger Reaction (CIR) identifier
# also
#	brutto (gross) formulas of substances
sub class_cir_brutto{
    my( $ce, $coef ) = @_;
    $ce || return;

    my( %elm, %bf, @cir );

    for my $c ( @$ce ){
	for my $s ( @$c ){

	    # stoichiometry coefficient
	    my $k = exists $coef->{$s} ? $coef->{$s} : 1; 

	    my %e = Chemistry::File::Formula->parse_formula( $s );

	    # for brutto
	    $bf{ $s } = join( '', map{ "$_$e{$_}" } sort { $a cmp $b } keys %e );

	    # for cir
	    push @cir, $k.$bf{ $s };

	    # For class
	    @elm{ keys %e } = ''; # reaction atoms
	}
    }

    # CLASS, CIR of reaction and hash: formula => brutto of substances
    return [ join( '', sort { $a cmp $b } keys %elm ),
	     ( cksum( join '+', sort { $a cmp $b } @cir ) )[0],
	     \%bf ];
}


# Transformation substance arrays to chemical mix (equation)
# $ce -- ref to array of substance arrays
# $opts ->{ }	 (facultative parameters)
#	->'substances' -- ref to array of real (required) substances
#	->'coefficients' -- ref to hash stoichiometry coefficients for substances
#	->'norma' -- chemical mix to brutto-normalize
sub prepare_mix{
    my( $ce, $opts ) = @_;

    # Check empty reactants & products
    croak('Bad equation!') if @$ce != 2 ||
	scalar( grep ! defined, @$ce ) ||
	scalar( grep { grep ! defined, @{$_} } @$ce );

    my $sign = 0;
    # Any coefficient isn't set --> to bypass
    if( exists( $opts->{'norma'} ) &&
	scalar( grep { 
		    grep ! exists( $opts->{'coefficients'}{$_} ), @{$_} 
		} @$ce ) == 0 ){ # All coefficients are set

	# Test stoichiometry coefficient sign  on initial (first) substances
	$sign = 1;
	for( @{ $ce->[0] } ){
	    $opts->{'coefficients'}{$_} || next; # Zero stoichiometry coefficient
	    $sign = -1 if $opts->{'coefficients'}{$_} < 0;
	    last;
	}
    }

    if( $sign != 0 ){ # chemical mix to brutto-normalize

	# if assume all coefficients positive '+'
	if( $opts->{'norma'} != 1 ){
	    $opts->{'coefficients'}{$_} *= -1 for @{ $ce->[1] };
	}

	my @cir; # for brutto-formula
	while( my($s, $c) = each %{ $opts->{'coefficients'} } ){
	    $c || next;
	    my $ip = $sign * $c > 0 ? 0 : 1;

	    my $ff = abs($c)." $s";
	    $cir[$ip]{$ff} = join '', Chemistry::File::Formula->parse_formula($ff);
	}
	# Result
	$_ = join(' == ', map{ join ' + ',sort {$_->{$a} cmp $_->{$b}} keys %{$_} } @cir);

    }else{
	if( exists( $opts->{'substances'} ) && @{ $opts->{'substances'} } ){
	    # List of real substances is specified
	    my %bs;
	    @bs{ @{ $opts->{'substances'} } } = ();

	    $_ = join(' == ', map{ join ' + ', map{ 
		if( exists $bs{$_} ){
		    exists( $opts->{'coefficients'}{$_} ) ? abs( $opts->{'coefficients'}{$_} )." $_" : $_
		}else{
		    ( )
		}
	    } @{$_} } @$ce );

	}else{	# List isn't specified
	    $_ = join(' == ', map{ join ' + ', map{ 
	    exists( $opts->{'coefficients'}{$_} ) ? abs( $opts->{'coefficients'}{$_} )." $_" : $_ } @{$_} } @$ce );
	}
    }

    s/^\s*==|==\s*$//g;
    /\S\s*[=+]+\s*\S/ ? $_ : return;
}


sub _search_atoms_subs{
    my $chem_eq = shift;

    my %tmp_subs;	# Atoms of substance
    my %atoms;		# Atom hash

    for my $i (@{$chem_eq}){
	for my $s (@{$i}){
	    # Atoms of substance
	    my %f = eval{ Chemistry::File::Formula->parse_formula($s) } or
croak("'$s' is not substance!");

	    for(keys %f){
		$tmp_subs{$s}{$_} = $f{$_};
		$atoms{$_}++; # Atom balance
	    }
	}
    }

    while( my($k,$v) = each %atoms){
	croak("No balance of '$k' atom!") if $v == 1;
    }

    # Atom (stoicheometry) matrix vectors (quantity of atoms for each substance)
    my %atoms_substance;
    for my $subs (keys %tmp_subs){
	$atoms_substance{$subs} = [ map { $tmp_subs{$subs}{$_} || 0 } keys %atoms ];
    }

    return( \%atoms_substance, scalar(keys %atoms) );
}


# Decomposes the chemical equation to
# arrays of initial substances and products
sub parse_chem_mix{
    $_ = shift; # List of substances with delimiters (spaces, comma, + )
    my $coef = shift; # hash of coefficients

    my %cf;	# temp hash of coefficients

    s/^\s+//;
    s/\s+$//;

    my $m = qr/\s*[ ,;+]\s*/;	# mask of delimeters

    # to unite the separeted numerals ( coefficient ? )
    1 while s/((?:$m|^)[1-9]+)$m([1-9]+(?:$m|$))/$1$2/g;

    # to unite the separeted substance & index
    s/([)}\]a-zA-Z1-9])\s+([1-9]+\s*[)}\]\-=+])/$1$2/g;

    # remove spaces around brackets
    s/([({\[])\s+/$1/g;
    s/\s+([)}\]])/$1/g;

    # The chemical equation is set:
			    # A + B --> C + D ||
			    # A, B, C, D
    my $chem_eq = /(.+?)\s*[=-]+>*\s*(.+)/ ?
	[ map [ split "$m" ], ($1,$2) ] :
	[ map [ split "$m" ], ( /(.+)$m(\S+)/ ) ];

    return unless @$chem_eq;

    for my $ip ( @$chem_eq ){

	my @ip_del; # For removal from an array of coefficients

	for(my $i=0; $i<=$#{ $ip }; $i++ ){
	    $_ = $ip->[$i];

	    if( /^(\d+)([({\[a-zA-Z].*)/ ){ # together coefficient and substance

		my ($c, $s) = ($1, $2); # coefficient, substance

		# zero coefficient
		if( $c =~ /^0$/ && ( $i==0 || ( $i>0 && $ip->[$i-1] =~ /\D/ ) ) ){ 
		    push @ip_del, $i; # remove substance

		}elsif( s/^0/O/ ){ # oxigen?
		    &_p_c_m( $_, $i, \%cf, $ip );

		}else{
		    $cf{$s} = $c;	# coefficient
		    $ip->[$i] = $s;	# substance
		}

	    }elsif( s/^0(.)/O$1/ ){ # oxigen
		&_p_c_m( $_, $i, \%cf, $ip );

	    }elsif( /^0$/ ){ # zero coefficient
		if( $i < $#{ $ip } && ! exists( $coef->{'zero2oxi'} ) ){ # remove
		    push @ip_del, $i; # coefficient
		    push @ip_del, ++$i; # substance

		}else{
		    s/^0/O/; # oxigen
		    &_p_c_m( $_, $i, \%cf, $ip );
		}

	    }elsif( /^\d+$/ ){	# only numerals
		# coefficient
		if( defined $ip->[$i+1] ){
		    $cf{ $ip->[$i+1] } = $_;
		
		}elsif( $ip eq $chem_eq->[0] &&
			 @{ $chem_eq->[1] } == 1 &&
			 $chem_eq->[1][0] =~ /[a-zA-Z]/ ){

		    # coefficient of product
		    $chem_eq->[1][0] = $_.$chem_eq->[1][0];
		}
		push @ip_del, $i;
	    }
	}
	splice @$ip, $_, 1 for( reverse @ip_del );
    }

    # To removal identical reactants and products
    for my $ip ( @$chem_eq ){

	my @ip_del;
	for(my $i = 0; $i < $#{ $ip }; $i++ ){

	    for(my $j = $i + 1; $j <= $#{ $ip }; $j++ ){

		if( $ip->[$i] eq $ip->[$j] ){
		    push @ip_del, $j;
		    last;
		}
	    }
	}
	splice @$ip, $_, 1 for( sort{ $b <=> $a } @ip_del );
    }

    # Check empty reactants
    if( ! @{ $chem_eq->[0] } ){ 
	return if @{ $chem_eq->[1] } < 2; # bad mix (one or no substance)
	push @{ $chem_eq->[0] }, shift @{ $chem_eq->[1] };
    }

    # To removal identical products with reactants
    for my $s ( @{ $chem_eq->[0] } ){
	my @ip_del;
	for(my $i=0; $i<=$#{ $chem_eq->[1] }; $i++ ){
	    push @ip_del, $i if $s eq $chem_eq->[1][$i];
	}
	splice @{ $chem_eq->[1] }, $_, 1 for( reverse @ip_del );
    }

    # Check empty products
    if( ! @{ $chem_eq->[1] } ){
	return if @{ $chem_eq->[0] } < 2; # bad mix (one or no substance)
	push @{ $chem_eq->[1] }, pop @{ $chem_eq->[0] };
    }

    @$coef{ keys %cf} = values %cf; # join (copy)

    delete $coef->{'zero2oxi'};

    # Lists of substances:
	# fist --- reactants or '=','-','>'
	# last --- products or '=','-','>'
    return $chem_eq;
}

sub _p_c_m{
    my( $s, $i, $cf, $ip ) = @_;

    if( exists $cf->{ $ip->[$i] } ){
	$cf->{$s} = $cf->{ $ip->[$i] };
	delete $cf->{ $ip->[$i] };
    }
    $ip->[$i] = $s; # replacement
}


# Calculation of oxidation state
sub oxidation_state{
    my $s = shift || return;

    my @species = $s =~ /$RE{balanced}{-parens=>'{}'}\d*/g;

    # One substance
    return &_in_os($s) if @species < 2 || $s ne join('',@species);

    my $r;	# Result:
	# HASH{element}{num}[0 .. n-1] - Element amount on everyone 1..n atom
	# HASH{element}{OS}[0 .. n-1][ .. ] - Oxidation States of Element (OSE) arrays 1..n atom 

    # Mix of substances
    for( @species ){

	# remove bordering brackets 
	s/^\{//;
	s/\}(\d*)$//;
	# save possible coefficient
	my $d = $1;
    
	my $p = &_in_os($_) || return;

	for my $e ( keys %$p ){
	    push @{ $r->{$e}{'OS'} }, @{ $p->{$e}{'OS'} };

	    if( $d ){
		$_ *= $d for @{ $p->{$e}{'num'} }
	    }
	    push @{ $r->{$e}{'num'} }, @{ $p->{$e}{'num'} };
	}
    }

    $r;
}

sub _in_os{
    my $chem_sub = shift;

    # prepare atomic composition of substance
    my %nf = eval{ Chemistry::File::Formula->parse_formula( $chem_sub ) };
    return unless keys %nf;

    # Count of "pure" atoms each element of substance
    $_ = $chem_sub;
    s/\d+//g;	# remove digits
    my %num = Chemistry::File::Formula->parse_formula( $_ );

    # Ions: { element }{ length }{ ion-pattern }[ [ array OSE ] ]
    my $ions = &_read_ions( $chem_sub );

    # Read Pauling electronegativity and OSE:
	# atom electronegativity, oxidation state, intermetallic compound
    my( $atom_el_neg, $atom_OS, $intermet ) = &_read_atoms( \%nf );
    return if keys( %$atom_el_neg ) != keys( %nf );

    my $prop;	# Result:

    # Substance is intermetallic compound or Simple substance (one element)
    if( $intermet || keys %nf == 1 ){

	while( my( $e, $n ) = each %nf ){
	    # Total quantity of atoms for element
	    $prop->{ $e }{ 'num' }[ 0 ] = $n;

	    # By default in the list of OSE only 0th charge
	    $prop->{ $e }{ 'OS' }[ 0 ] = [ 0 ];
	}

	return $prop ;
    }

    # Sort atoms in decreasing order of electronegativity:
    # 1th --- the most electronegative
    my @neg = sort { $atom_el_neg->{$b} <=> $atom_el_neg->{$a} } keys %{ $atom_el_neg };

    my %bOS;	# by default OSE basic list

    # Basic OSE list of atoms on decrease of electronegativities
    for(my $i = 0; $i <= $#neg; $i++){

	my $e = $neg[$i];	# element

	# Electronegative 1th is identical with next elements
	if( ( $i < $#neg &&
	     $atom_el_neg->{ $neg[0] } == $atom_el_neg->{ $neg[$i+1] } ) ||
	     $i == 1 ){

	    # '-' and '+' OSE, without 0
	    $bOS{ $e } = [ grep $_, @{ $atom_OS->{$e} } ];

	}elsif( $i == 0 ) { # 1th (most electronegative) -> only '-' OSE
		$bOS{ $e } = [ grep $_ < 0, @{ $atom_OS->{$e} } ];

	}else{	# Others -> only '+' OSE
	    $bOS{ $e } = [ grep $_ > 0, @{ $atom_OS->{$e} } ];
	}

	# Inert elements
	$bOS{ $e } = [ @{ $atom_OS->{$e} } ] if $e=~/He|Ne|Ar|Kr|Xe|Rn/;

	# mask for search ions
	my $m = length($e)==1 ? "$e\\d+|$e(?![a-gik-pr-u])" : "$e\\d*";

	for(my $j = 0; $j < $num{$e}; $j++){

	    # Number of various atoms for element in substance
	    if( $num{$e} == 1 ){ # One atom of element in substance
	        push @{ $prop->{$e}{'num'} }, $nf{$e};

	    }else{
		my $count = 0;
		$_ = $chem_sub;

		# Search ion-group. Remove all atoms of element, except current
		s{ ($m) }{ $1 if $count++ == $j }gex;

		my %f = Chemistry::File::Formula->parse_formula($_);
		push @{ $prop->{$e}{'num'} }, $f{$e};
	    }
	}
    }

    # Two pass: 1st -- ion recognition, 0th -- without ions (possible)
    for my $yni (1, 0){
	my $no_ion = 1;		# no ions

	my $balance_A = 0;	# for Electronic balance
	my $max_n_OS = 0;	# Number of OSE in maximum list
	my @atoms;		# Varied atoms of elements
	my %osin;		# lists of OSE ions

	for(my $i = 0; $i <= $#neg; $i++){

	    my $e = $neg[$i];	# element

	    # mask for search ions
	    my $m = length($e)==1 ? "$e\\d+|$e(?![a-gik-pr-u])" : "$e\\d*";

_SO_M1:		# Number of various atoms for element in substance
	    for(my $j = 0; $j < $num{$e}; $j++){

		$_ = $chem_sub;

		my $count = 0;
		# Search ion-group. Remove all atoms of element, except current
		s{ ($m) }{ $1 if $count++ == $j }gex;

		if( $yni ){
		    # Sort by decrease length of ion-group
		    for my $l (sort {$b <=> $a} keys %{ $ions->{$e} } ) {

			for my $mg ( keys %{ $ions->{$e}{$l} } ){
			    next unless /$mg/; # Ion-group isn't found

			    $no_ion = 0; # yes ions

			    # Ion-group is found. Save list of OSE
			    # for j-th atom of element
			    if( @{ $ions->{$e}{$l}{$mg} } == 1 ){ # One list OSE ion 

				push @{ $prop->{$e}{'OS'} }, $ions->{$e}{$l}{$mg}[0];

				# Calculation total and mean OSE
				my $os;
				$os += $_ for @{ $prop->{$e}{'OS'}[$j] };
			
				# sum OSE * number of atoms / number of OSE
				$balance_A += $os * $prop->{$e}{'num'}[$j] / @{ $prop->{$e}{'OS'}[$j] };

			    }else{ # Many OSE ion lists
				# Add in array varied OSE for j-th atom of element
				push @atoms, "$e:$j";
				$osin{"$e:$j"} = $ions->{$e}{$l}{$mg};

				# Define from a basic list of OSE
				push @{ $prop->{$e}{'OS'} }, [ -999 ];

				# Quantity of OSE from basic list
				my $n_OS = $#{ $ions->{$e}{$l}{$mg} };
				$max_n_OS = $n_OS if $n_OS > $max_n_OS; # max list of OSE
			    }
			    next _SO_M1; # Ion-group is found
			}
		    }
		}

		# Quantity of OSE from basic list
		my $n_OS = $#{ $bOS{ $e } };
		$max_n_OS = $n_OS if $n_OS > $max_n_OS; # max list of OSE

		if( $n_OS ) { # number of OSE > 1
		    # Add in array varied OSE for j-th atom of element
		    push @atoms, "$e:$j";

		    # Define from a basic list of OSE
		    push @{ $prop->{$e}{'OS'} }, [ -999 ];

		}else{ # One OSE in list
		    push @{ $prop->{$e}{'OS'} }, [ $bOS{ $e }[0] ];

		    # charge * number of atoms
		    $balance_A += $bOS{ $e }[0] * $prop->{$e}{'num'}[$j];
		}
	    }
	}

	my $balance_B = 0;	# for Electronic balance

	# Select oxidation states
	if( $max_n_OS ){
	    my $iter = variations_with_repetition( [ (0..$max_n_OS) ], scalar( @atoms ) );
_SO_M2:
	    while (my $p = $iter->next) {

		$balance_B = 0;
		for(my $i = 0; $i<=$#{ $p }; $i++){

		    my $x = $atoms[$i];
		    my($e, $j) = split /:/,$x;

		    my($sum, @os);

		    if( exists $osin{ $x } ){ # Some OSE ion lists

			$sum += $_ for @{ $osin{ $x }[ $p->[$i] ] };
			@os = @{ $osin{ $x }[ $p->[$i] ] };

		    }else{
			$os[0] = $sum = $bOS{ $e }[ $p->[$i] ];
		    }

		    next _SO_M2 unless defined $sum; # OSE have ended

		    # sum OSE * number of atoms / number of OSE
		    $balance_B += $sum * $prop->{ $e }{'num'}[$j] / @os;
		    $prop->{ $e }{'OS'}[$j] = [ @os ];

		}
		last unless $balance_A + $balance_B; # balance is found
	    }
	}

	return if $no_ion && ($balance_A + $balance_B); # balance is not found

	$balance_A = 0; # for electronic balance

	# Check electronic balance
	for my $e (keys %$prop ){
	    my $i=0;
	    for my $os ( @{ $prop->{$e}{'OS'} } ){

		my $sum;
		$sum += $_ for @$os;

		# sum OSE * number of atoms / number of OSE
		$balance_A += $sum * $prop->{$e}{'num'}[ $i++ ] / @$os;
	    }
	}

	if( $balance_A ){
	    return if $no_ion;
	}else{
	    return $prop;
	}
	delete $prop->{$_}{'OS'} for keys %$prop;
    }
}

# Read Pauling electronegativity and OSE
# only for given elements of substance
# input:
#	%atoms -- elements
# return:
#	%atom_el_neg
#	%atom_OS
#	$intermet

sub _read_atoms{
    my $atoms = shift;

    my %atom_el_neg;	# atom electronegativity
    my %atom_OS;	# oxidation state
    my $intermet = 1;	# for intermetallic compound

    open PERIODIC;
    while(<PERIODIC>){
	s/\s*#.*//g;		# Delete comments
	next if /^\s*$/;	# To discard blank lines
	chomp;
	my ($e, $neg, $metal, $os) = split /\s+/;

	next if !defined $e || !exists $atoms->{ $e };

	$atom_el_neg{ $e } = $neg;
	$atom_OS{ $e } = [ split ';',$os ];
	$intermet = 0 unless $metal;	# Not intermetallic compound
    }
    close PERIODIC;

    \%atom_el_neg, \%atom_OS, $intermet;
}

# Read necessary ion-group
# input:
#	$Chemistry_substance
# return:
#	$ions
sub _read_ions {
    my $chem_sub = shift;
    my %ions;

    open IONS;

    # Construct pattern
    while(<IONS>){
	chomp;
	s/\s*#.*//g;
	next if /^\s*$/;

	my ($frm, $os) = split /\s+/; # formula (mask) and OSE list
	my %a = split /_|=/,$os; # Parse to element end OSE

	if($os =~ /~/){ # Macro-substitutions

	    my %ek;
	    my $max_n_ek = 0; # max number of element-pattern in macro-substitutions

	    while( my($e, $v) = each %a ){

		if($e =~ /(\w+~)(.*)/){
		    $ek{$1}[0] = [ split ',',$2 ]; # elements
		    $ek{$1}[1] = $v; # OSE for group

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

		    $m =~ s/$em/$e/g; # Construct ion mask
		}

		next unless $chem_sub =~ /($m)/; # Ions in substance aren't present

		my $l = length($1); # Length of ion mask

		$i = 0;
		for my $em (sort keys %ek){
		    my $e = $ek{ $em }[0][ $p->[$i++] ]; # element

		    for my $z ( split /!/, $ek{ $em }[1] ){
			# list OSE
			push @{ $ions{ $e }{ $l }{ $m } }, [ split /;/,$z ];
		    }
		}

		while(my ($e, $v) = each %a ){
		    next if $e =~ /~/;

		    # list OSE
		    for my $z ( split /!/, $v ){
			push @{ $ions{ $e }{ $l }{ $m } }, [ split /;/,$z ];
		    }
		}
	    }

	}else{
	    next unless $chem_sub =~ /($frm)/; # no ions in substance

	    my $l = length($1); # Length of the found group

	    while(my ($e, $v) = each %a ){
		# list OSE
		for my $z ( split /!/, $v ){
		    push @{ $ions{ $e }{ $l }{ $frm } }, [ split /;/,$z ];
		}
	    }
	}
    }
    close IONS;

    \%ions;
}


# Pauling scale (adapted)
# Attention!
#	order of OSE is important (last are exotic OSE)
__PERIODIC__
Ac	110	1	0;3
Ag	193	1	0;1;2;3;5
Al	161	1	-3;0;1;2;3
Am	113	1	0;2;3;4;5;6
Ar	0	0	0
As	221	0	-3;0;3;5	# 2
At	225	0	-1;0;1;5;7	# 3
Au	254	1	0;1;2;3;5;7	# -1
B	204	0	-3;0;1;2;3
Ba	89	1	0;2
Be	157	1	0;2
Bh	0	1	0;7
Bi	221	0	-3;0;2;3;5
Bk	130	1	0;3;4
Br	296	0	-1;0;1;3;4;5;6;7
C	255	0	-4;-3;-1;0;2;3;4	# -2;1
Ca	100	1	0;2
Cd	169	1	0;2
Ce	112	1	0;3;4		# 2
Cf	130	1	0;2;3;4
Cl	316	0	-1;0;1;3;4;5;6;7	# 2
Cm	128	1	0;3;4
Co	188	1	0;1;2;3;4	# -1; 5
Cr	166	1	0;1;2;3;4;5;6	# -2;-1
Cs	79	1	0;1
Cu	190	1	0;1;2;3		# 4
D	220	0	-1;0;1
Db	0	1	0;5
Ds	0	1	0
Dy	122	1	0;3;4		# 2
Er	124	1	0;3
Es	130	1	0;2;3
Eu	120	1	0;2;3
F	400	0	-1;0
Fe	183	1	0;2;3;6;8;4	# -2;-1; 1; 5
Fm	130	1	0;2;3
Fr	70	1	0;1
Ga	181	1	0;1;2;3
Gd	120	1	0;3		# 1; 2
Ge	201	0	-4;-2;0;2;4	# 1; 3
H	220	0	-1;0;1
He	0	0	0
Hf	130	1	0;2;3;4
Hg	200	1	0;1;2		# 4
Ho	123	1	0;3
Hs	0	1	0;7
I	266	0	-1;0;1;3;5;7
In	178	1	0;1;2;3
Ir	220	1	0;1;2;3;4;5;6;8	# -3;-1
K	82	1	0;1
Kr	0	0	0;2;4;6
Ku	0	1	0
La	110	1	0;3		# 2
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
Nd	114	1	0;3		# 2
Ne	0	0	0
Ni	191	1	0;2;3;4;1	# -1
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
Pr	113	1	0;3;4		# 2
Pt	228	1	0;2;3;4;5;6;1
Pu	128	1	0;2;3;4;5;6	# 7
Ra	90	1	0;2;4
Rb	82	1	0;1
Re	190	1	0;1;2;3;4;5;6;7	# -3;-1
Rf	0	1	0;4
Rg	0	1	0
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
T	220	0	-1;0;1
Ta	150	1	0;1;2;3;4;5	# -1
Tb	110	1	0;3;4		# 1
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
Y	122	1	0;3		# 1; 2
Yb	110	1	0;2;3
Zn	165	1	0;2
Zr	133	1	0;2;3;4		# 1

__IONS__
# Attention!
#	ion-group mask consist individual atoms only

# hydroxide
[^O]OH(?![efgos])	H=1_O=-2

.a~O		a~Cl,Br=1_O=-2
.IO		I=1!3_O=-2
# nitrites, meta- antimonites, arsenites and others
.a~O2		a~N,Sb,Al,As,Au,Cl,Br,B=3_O=-2
.BO3		B=3_O=-2
# carbonates, selenates, tellurates
.a~O3		a~C,Se,Si,Te,Pt,Mo,Po,Mn=4_O=-2
# bismuthates, nitrates  and others
.a~O3		a~Bi,N,V,Cl,Br,I=5_O=-2
# plumbates, silicates
.a~O4		a~Pb,Si=4_O=-2
# ortho- antimonates, arsenates, phosphates and others
.a~O4		a~Sb,As,P,V=5_O=-2
# molybdates, tungstates, chromates and others (excepting peroxides)
.a~O4(?=[^O]|Os|$)	a~Kr,U,S,Se,Te,Mo,W,Cr=6_O=-2
# per- chlorates, bromates, iodates
.a~O4		a~Cl,Br=7_O=-2
# rhodanides (thiocyanates) and for selenium
.(?:a~CN|a~NC|CNa~|Ca~N|Na~C|NCa~)(?![a-gik-pr-u])	a~S,Se=-2_C=4_N=-3
# ortho-/meta- : /phosphi(-a)tes, antimoni(-a)tes, arseni(-a)tes
.a~O3		a~P,Sb,As=5!3_O=-2

.a~O4		a~I,Re=6!7_O=-2
.a~O4		a~Tc,Ru=5!6!7_O=-2
.MnO4		Mn=3!4!5!6!7_O=-2

# ferrate
.FeO4		Fe=3!4!6_O=-2

.IO[56]		I=7_O=-2
^I2O4$		I=3;5_O=-2

.TeO6		Te=6_O=-2

.XeO6		Xe=6!8_O=-2

.MoO3F3		Mo=6_F=-1_O=-2

# sulphites
.SO3(?=[^OS]|Os|S[bcegimnr]|$)		S=4_O=-2
# thiosulphates
.S2O3		S=6;-2_O=-2
# pirosulphates
.S2O7		S=6_O=-2
# peroxydisulfuric (marshal's) acid
.S2O8		S=6_O=-2;-2;-2;-2;-2;-2;-1;-1
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

.BF4		B=3_F=-1

.NH2Br		H=1_N=-3_Br=-1

#.P\d+O\d+	P=5_O=-2	# polyphosphates

# Neutral ligands
CO\(NH2\)2		C=4_H=1_N=-3_O=-2
H2O(?=[^2O]|Os|$)	H=1_O=-2
C2H4			C=-2_H=1

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
^U3O8$		U=5;5;6_O=-2	# triuranium octoxide
^Pb2O3$		Pb=2;4_O=-2
^a~3O4$		a~Pb,Pt=2;2;4_O=-2
^a~3O4$		a~Fe,Co,Mn=2;3;3_O=-2
# carbonyls
^a~\d*\(CO\)\d*$	a~V,W,Cr,Ir,Mn,Fe,Co,Ni,Mo,Tc,Re,Ru,Rh,Os=0_C=2_O=-2
# alkaline metals and others
^a~2O2			a~H,Li,Na,K,Rb,Cs,Fr,Hg=1_O=-1	# peroxides
^(?:a~O2|a~2O4)		a~Li,Na,K,Rb,Cs,Fr=1_O=-1;0	# superoxides
^a~O3			a~Li,Na,K,Rb,Cs,Fr=1_O=-1;0;0	# ozonide
# alkaline-earth metals and others
^a~O2			a~Mg,Ca,Sr,Ba,Ra,Zn,Cd,Hg,Cu=2_O=-1	# peroxides
^(?:a~\(O2\)2|a~O4)	a~Mg,Ca,Sr,Ba,Ra=2_O=-1;0	# superoxides
^(?:a~\(O3\)2|a~O6)	a~Mg,Ca,Sr,Ba,Ra=2_O=-1;0;0	# ozonide
# all peroxides
.\(O2\)			O=-1
# dioxygenils, O2PtF6 ... (except O2F2)
^(?:\(O2\)|O2)(?![F])	O=1;0
# chromium peroxide
^CrO5$		Cr=6_O=-2;-1;-1;-1;-1
# sulfur peroxide
^SO4$		S=6_O=-2;-2;-1;-1
^S2O7$		S=6_O=-2;-2;-2;-2;-2;-1;-1
# peroxymonosulfuric | persulfuric | Caro's acid
.SO5		S=6_O=-2;-2;-2;-1;-1
# per-carbonates (percarbonic acid)
.C2O6		C=4_O=-2;-2;-2;-2;-1;-1
# acid chlorine peroxide ?
.ClO5		Cl=7_O=-2;-2;-2;-1;-1

^Cl2O8$		Cl=7_O=-2;-2;-2;-2;-2;-2;-1;-1
^I2O8$		I=7_O=-2;-2;-2;-2;-2;-2;-1;-1
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

Transformation of the chemical mix in reagent and product arrays:

  my $chemical_equation = 'KMnO4 + NH3 --> N2 + MnO2 + KOH + H2O';
  print Dumper parse_chem_mix( $chemical_equation );

Will print:

  $VAR1 = [
           ['KMnO4', 'NH3'],
           ['N2', 'MnO2', 'KOH','H2O']
          ];

Preparation of the chemical mix (equation) from reagent and product arrays:

  my $ce = [ [ 'K', 'O2'], [ 'K2O', 'Na2O2', 'K2O2', 'KO2' ] ];
  my $k = { 'K2O' => 1, 'Na2O2' => 0, 'K2O2' => 2, 'KO2' => 3 };
  print prepare_mix( $ce, { 'coefficients' => $k } ),"\n";

Will output:

  K + O2 == 1 K2O + 0 Na2O2 + 2 K2O2 + 3 KO2

'Synthesis' of the good :) chemical formula(s):

  my $abracadabra = 'ggg[crr(cog(nhz2)2)6]4[qcr(cn)5j]3qqq';
  print Dumper good_formula( $abracadabra );

Will output:

  $VAR1 = [
           '[Cr(CO(NH2)2)6]4[Cr(CN)5I]3',
           '[Cr(Co(NH2)2)6]4[Cr(CN)5I]3'
          ];

Calculation CLASS-CIR and brutto (gross) formulas of substances
for reaction. See example:

  my $mix = '2 KMnO4 + 5 H2O2 + 3 H2SO4 --> 1 K2SO4 + 2 MnSO4 + 8 H2O + 5 O2';
  my %cf;
  my $ce = parse_chem_mix( $mix, \%cf );
  print Dumper class_cir_brutto( $ce, \%cf );

Will output:

  $VAR1 = [
          'HKMnOS',
          1504979632,
          {
            'O2' => 'O2',
            'MnSO4' => 'Mn1O4S1',
            'KMnO4' => 'K1Mn1O4',
            'K2SO4' => 'K2O4S1',
            'H2SO4' => 'H2O4S1',
            'H2O2' => 'H2O2',
            'H2O' => 'H2O1'
          }
        ];

TTC reaction. Proceeding example above:

  print Dumper ttc_reaction( $ce );

Will output:

  $VAR1 = {
          'r' => 5,
          'a' => 5,
          's' => 7
        };


=head1 DESCRIPTION

The module provides the necessary subroutines to solve some puzzles of the
general inorganic and physical chemistry. The methods implemented in this module,
are all oriented to known rules and laws of general and physical chemistry.

=head1 SUBROUTINES

Chemistry::Harmonia provides these subroutines:

    oxidation_state( $formula_of_substance )
    parse_chem_mix( $mix_of_substances [, \%coefficients ] )
    good_formula( $abracadabra [, { 'zero2oxi' => 1 } ] )
    prepare_mix( \@reactants_and_products [, \%facultative_parameters ] )
    class_cir_brutto( \@reactants_and_products [, \%coefficients ] )
    ttc_reaction( \@reactants_and_products )

All of them are context-sensitive.


=head2 oxidation_state( $formula_of_substance )

This subroutine returns a hierarchical hash-reference of hash integer 
oxidation state (key 'OS') and hash with the number of atoms for 
each element (key 'num') for the inorganic C<$formula_of_substance>.

Always use the upper case for the first character in the element name
and the lower case for the second character from Periodic Table. Examples: Na,
Ag, Co, Ba, C, O, N, F, etc. Compare: Co - cobalt and CO - carbon monoxide.

For very difficult mysterious formula (usually organic) returns C<undef>.
It will be good if to set, for example, 'Pb3C2O7' and 'Pt2Cl6' as
'{PbCO3}2{PbO}' and '{PtCl2}{PtCl4}'.

If you doesn't know formulas of chemical elements and/or Periodic Table
use subroutine C<good_formula()>.
I insist to do it always anyway :)

Now C<oxidation_state()> is checked over 6200 unique inorganic substances.


=head2 parse_chem_mix( $mix_of_substances [, \%coefficients ] )

A chemical equation consists of the chemical formulas of the reactants
and products. This subroutine parses C<$mix_of_substances> (usually chemical equation)
to arrays of the reactants (initial substances) and products
(substances formed in the chemical reaction).
It is the most simple and low-cost way to carry out reaction without
reactants :).

Separator of the reactants from products can be sequence '=', '-' 
together or without one or some '>'. For example: 
=, ==, =>, ==>, ==>>, -, --, ->, -->, ->>> etc.
Spaces round a separator are not essential.
If the separator is not set, last substance of a mix will be a product only.

Each individual substance's chemical formula is separated from others by a plus
sign ('+'), comma (','), semicolon (';') and/or space.
Valid examples:

  print Dumper parse_chem_mix( 'KNO3 + S ; K2SO4 , NO SO2' );

Will print:

  $VAR1 = [
            [ 'KNO3','S','K2SO4','NO' ],
            [ 'SO2' ]
        ];

If in C<$mix_of_substances> is stoichiometric coefficients they collect in ref to hash
C<\%coefficients>. Next example:

  my %coef;
  my $chem_eq = 'BaS + 2 H2O = Ba(OH)2 + 1 Ba(SH)2';

  my $out_ce = parse_chem_mix( $chem_eq, \%coef );
  print Dumper( $out_ce, \%coef );

Will print something like:

  $VAR1 = [  [ 'BaS', 'H2O'], [ 'Ba(OH)2', 'Ba(SH)2'] ];
  $VAR2 = { 
       'Ba(SH)2' => '1',
      'H2O' => '2'
   };

By zero (0) coefficients it is possible to eliminate substances from the mix.
Next example:

  my $chem_eq = '2Al O2 = Al2O3 0 CaO*Al2O3';

Will output like:

  $VAR1 = [ [ 'Al', 'O2' ], [  'Al2O3' ] ];
  $VAR2 = {  'Al' => '2' };

However:

  $chem_eq = '2Al O2  Al2O3 0 CaO*Al2O3';

Will output like:

  $VAR1 = [ [ 'Al', 'O2', 'Al2O3', 'O' ], [  'CaO*Al2O3' ] ];
  $VAR2 = {  'Al' => '2' };

As without a separator ('=' or others similar) the last substance will be a product.

If in C<$mix_of_substances> is zero (0) similar oxygen, they are replaced
oxygen. Certainly, oxygen is life. I love oxygen :)
Some more examples:

  $chem_eq = '2Al 02 Ca CaO*Al2O3';

Will output like:

  $VAR1 = [ [ 'Al', 'O2', 'Ca' ], [ 'CaO*Al2O3' ] ];
  $VAR2 = { 'Al' => '2' };

Input:

  $chem_eq = '2Al 102 Ca CaO*Al2O3';

Output:

  $VAR1 = [ [ 'Al', 'Ca' ], [ 'CaO*Al2O3' ] ];
  $VAR2 = { 'Al' => '2', 'Ca' => '102' };

Input:

  $chem_eq = '2Al --> 0 0Al2O3 0';

Output:

  $VAR1 = [ [ 'Al' ], [ 'O' ] ];
  $VAR2 = { 'Al' => '2' };

Input:

  $chem_eq = 'Al O2 = 1 0Al2O3';

Output:

  $VAR1 = [ [ 'Al', 'O2' ], [  'OAl2O3' ] ];
  $VAR2 = { 'OAl2O3' => '1' };

The forced conversion of single zero to oxygen is set by
parameter C<'zero2oxi'>. It add in C<\%coefficients>. Next example:

  $coef{ 'zero2oxi' } = 1;
  $chem_eq = 'Al CaO = 0 Al2O3';

Output:

  $VAR1 = [ ['Al', 'CaO'], ['O', 'Al2O3'] ];

Without C<'zero2oxi'> output:

 $VAR1 = [ ['Al'], ['CaO'] ];

Actually the subroutine recognizes more many difficult situations.
Here some examples:

  '2Al 1 02 Ca Al2O3' to-> [ ['Al', 'O2', 'Ca'], ['Al2O3'] ], {'Al' => 2, 'O2' => 1}
  '2Al 102 Ca Al2O3'  to-> [ ['Al', 'Ca'], ['Al2O3'] ], {'Al' => 2, 'Ca' => 102}
  '2Al 1 02 4O2 = 1 0Al2O3' to-> [ ['Al', 'O2'], ['OAl2O3'] ], {'Al' => 2, 'O2' => 4, 'OAl2O3' => 1}
  '2Al = 00 Al2O3'  to-> [ ['Al'], ['O0', 'Al2O3'] ], {'Al' => 2}
  '2Al O 2 = Al2O3'  to-> [ ['Al', 'O2'], ['Al2O3'] ], {'Al' => 2}
  '2Al O = '  to-> [ ['Al', 'O'], ['='] ], {'Al' => 2}
  ' = 2Al O'  to-> [ ['=','Al'], ['O'] ], {'Al' => 2}
  '0Al = O2 Al2O3'  to-> [ ['O2'], ['Al2O3'] ]
  '2Al 1 2 3 4 Ca 5 6 Al2O3 7 8 9'  to-> [ ['Al', 'Ca'], ['Al2O3'] ], {'Al2O3' => 56, 'Al' => 2, 'Ca' => 1234}
  '2Al 1 2 3 4 Ca 5 6 Al2O3'  to-> [ ['Al', 'Ca'], ['Al2O3'] ], {'Al2O3' => 56, 'Al' => 2, 'Ca' => 1234}
  '2Al 1 2 3 4 Ca 5 6 = Al2O3'  to-> [ ['Al', 'Ca56'], ['Al2O3'] ], {'Al' => 2, 'Ca56' => 1234}
  '2Al 1 2 3 4 Ca 5 6 = Al2O3 CaO 9'  to-> [ ['Al', 'Ca56'], ['Al2O3', 'CaO'] ], {'Al' => 2, 'Ca56' => 1234}
  'Al O + 2 = Al2O3'  to-> [ ['Al', 'O'], ['Al2O3'] ], {'Al2O3' => 2}
  'Cr( OH )  3 + NaOH = Na3[ Cr( OH )  6  ]'  to-> [ ['Cr(OH)3', 'NaOH'], ['Na3[Cr(OH)6]'] ]


=head2 good_formula( $abracadabra [, { 'zero2oxi' => 1 } ] )

This subroutine parses C<$abracadabra> to array reference of "good" chemical
formula(s). The "good" formula it does NOT mean chemically correct.
The subroutine C<oxidation_state()> will help with a choice chemically
correct formula.

Algorithm basis is the robust sense and chemical experience.

  'Co'   to->  'Co'
  'Cc'   to->  'CC'
  'co'   to->  'CO', 'Co'
  'CO2'  to->  'CO2'
  'Co2'  to->  'Co2', 'CO2'
  'mo2'  to->  'Mo2'

The good formula(s) there are chemical elements, brackets ()[]{} and
digits only. C<good_formula()> love oxygen.
Fraction will be scaled in the integer.

Fragments A*B, xC*yD are transformed to {A}{B}, {C}x{D}y
(here A, B, C, D - groups of chemical elements, digits and brackets ()[]{};
x, y - digits only). Next examples:

  '0.3al2o3*1.5sio2'  to->  '{Al2O3}{SIO2}5', '{Al2O3}{SiO2}5'
  'al2(so4)3*10h20'   to->  '{Al2(SO4)3}{H20}10'
  '..,,..mg0,,,,.*si0...s..,..'  to->  '{MgO}{SIOS}', '{MgO}{SiOS}'

Superfluous brackets won't be:

  'Irj(){}[]'  to->  'IrI'
  '[{(na)}]'   to->  'Na'

However:

  '{[[([[CaO]])*((SiO2))]]}'  to->  '{([[CaO]])}{((SiO2))}'

If in C<$abracadabra> is zero (0) similar oxygen, they are replaced oxygen.
I love the oxygen is still :)
Next examples:

  '00O02'  to->  'OOOO2'
  'h02'    to->  'Ho2', 'HO2'

However:

  'h20'    to->  'H20'

The forced conversion of zero to oxygen is set by parameter C<'zero2oxi'>:

  my $chem_formulas = good_formula( 'h20', { 'zero2oxi' => 1 } );

Output C<@$chem_formulas>:

  'H20', 'H2O'

If mode of paranoiac is necessary, then transform C<$abracadabra>
to low case as:

    lc $abracadabra

Beware use very long C<$abracadabra>!


=head2 prepare_mix( \@reactants_and_products [, \%facultative_parameters ] )

This subroutine simple but useful. It forms the chemical mix (equation)
from ref to array of arrays C<\@reactants_and_products>,
i.e. is C<parse_chem_mix> antipode.

The following can be  C<\%facultative_parameters>:
C<'substances'> - ref to array of real (required) substances,
C<'coefficients'> - ref to hash stoichiometry coefficients for substances.
Full examples:

  my $ce = [ [ 'O2', 'K' ], [ 'K2O', 'Na2O2', 'K2O2', 'KO2' ] ];
  my $k = { 'K' => 2, 'K2O2' => 1, 'KO2' => 0 };

  my $mix = prepare_mix( $ce, { 'coefficients' => $k } );

Will output C<$mix>:

  O2 + 2 K == K2O + Na2O2 + 1 K2O2 + 0 KO2

For real substances:

  my $real = [ 'K', 'O2', 'K2O2', 'KO2' ];
  print prepare_mix( $ce, { 'coefficients' => $k, 'substances' => $real } );

Will print:

  O2 + 2 K == 1 K2O2 + 0 KO2


=head2 class_cir_brutto( \@reactants_and_products [, \%coefficients ] )

This subroutine calculates Unique Common Identifier of Reaction 
C<\@reactants_and_products> with stoichiometry C<\%coefficients>
and brutto (gross) formulas of substances, i.e ref to array:
0th - alphabetic CLASS, 1th - Chemical Integer Reaction Identifier (CIR),
2th - hash brutto substances.

  my $reaction = '1 H2O + 1 CO2 --> 1 H2CO3';
  my %cf;
  my $ce = parse_chem_mix( $reaction, \%cf );
  print Dumper class_cir_brutto( $ce, \%cf );

Will print

  $VAR1 = [
          'CHO',
          1334303561,
          {
            'H2CO3' => 'C1H2O3',
            'CO2' => 'C1O2',
            'H2O' => 'H2O1'
          }
        ];

CIR is a 32 bit CRC of normalized chemical equation,
generating the same CRC value as the POSIX GNU C<cksum> program.
The returned CIR will always be a non-negative integer
in the range 0..2^32-1, i.e. 0..4,294,967,295.

The nature is diversiform, but we search simple decisions :)

The C<class_cir_brutto()> protesting CLASS-CIR
over 22,100 unique inorganic reactions.
Yes, to me it was hard to make it.


=head2 ttc_reaction( \@reactants_and_products )

This subroutine calculates Tactico-Technical characteristics (TTC)
of reaction C<\@reactants_and_products>, sorry military slang :),
i.e. quantity SAR: (s)ubstance, (a)toms and (r)ank of reaction.
Proceeding example above:

  print Dumper ttc_reaction( $ce );

Will output:

  $VAR1 = {
          'r' => 2,
          'a' => 3,
          's' => 3
        };


=head2 EXPORT

Chemistry::Harmonia exports nothing by default.
Each of the subroutines can be exported on demand, as in

  use Chemistry::Harmonia qw( oxidation_state );

the tag C<redox> exports the subroutines C<oxidation_state>,
C<parse_chem_mix> and C<prepare_mix>:

  use Chemistry::Harmonia qw(:redox);

the tag C<equation> exports the subroutines C<good_formula>,
C<parse_chem_mix>, C<prepare_mix>, C<class_cir_brutto> and
C<ttc_reaction>:

  use Chemistry::Harmonia qw(:equation);

and the tag C<all> exports them all:

  use Chemistry::Harmonia qw(:all);


=head1 DEPENDENCIES

Chemistry::Harmonia is known to run under perl 5.8.8 on Linux.
The distribution uses L<Chemistry::File::Formula>,
L<Algorithm::Combinatorics>,
L<Regexp::Common>,
L<Math::BigInt>,
L<Math::BigRat>,
L<Math::Assistant>,
L<String::CRC::Cksum>,
L<Inline::Files>
and L<Carp>.


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
