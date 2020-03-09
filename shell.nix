with import <nixpkgs> {};

let
  pythonEnv = python37.withPackages (ps: [
    ps.z3
    ps.pip
  ]);
in mkShell {
  buildInputs = [ z3 pythonEnv ];
  shellHook = ''
            alias pip="PIP_PREFIX='$(pwd)/_build/pip_packages' \pip"
            export PYTHONPATH="$(pwd)/_build/pip_packages/lib/python3.7/site-packages:$PYTHONPATH"
            unset SOURCE_DATE_EPOCH
  '';
  }
