use 5.008008;
use ExtUtils::MakeMaker;

WriteMakefile(
    NAME              => 'Chemistry::Harmonia',
    VERSION_FROM      => 'lib/Chemistry/Harmonia.pm',
    PREREQ_PM         => {
            'Algorithm::Combinatorics'	=> '0.26',
            'Chemistry::File::Formula'	=> '0.37',
	    'String::CRC::Cksum'	=> '0.91',
	    'Math::Assistant'	=> '0.04',
	    'Regexp::Common'	=> '2011041701',
	    'Math::BigInt'	=> '1.993',
	    'Math::BigRat'	=> '0.2602',
            'Inline::Files'	=> '0.64',
            'Carp'		=> '0',
            'Test::More'	=> '0',
    },
    dist => {
        COMPRESS => 'gzip -9f',
        SUFFIX => 'gz',
    },
    ($] >= 5.005 ?     ## Add these new keywords supported since 5.005
      (ABSTRACT_FROM  => 'lib/Chemistry/Harmonia.pm',
       AUTHOR         => 'Alessandro Gorohovski <angel@feht.dgtu.donetsk.ua>') : ()),
);
