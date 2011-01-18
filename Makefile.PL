use 5.008008;
use ExtUtils::MakeMaker;

WriteMakefile(
    NAME              => 'Chemistry::Harmonia',
    VERSION_FROM      => 'lib/Chemistry/Harmonia.pm',
    PREREQ_PM         => {
            'Algorithm::Combinatorics'	=> '0.25',
            'Chemistry::File::Formula'	=> '0.37',
            'Inline::Files'	=> '0.63',
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
