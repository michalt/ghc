if default_testopts.cleanup != '':
   cleanup = 'CLEANUP=1'
else:
   cleanup = ''

def normaliseContainersPackage(str):
    return re.sub('containers-[^@]+@conta_[A-Za-z0-9]+', 'containers-<VERSION>@conta_<HASH>', str)

test('cabal07',
     normalise_errmsg_fun(normaliseContainersPackage),
     run_command,
     ['$MAKE -s --no-print-directory cabal07 ' + cleanup])
