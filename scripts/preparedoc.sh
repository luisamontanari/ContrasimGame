#!

# meant to be called from the isabelle theory directory
~/Software/Isabelle2021/bin/isabelle build -d . Contrasimulation
mkdir -p html
rsync -a ~/.isabelle/Isabelle2021/browser_info/Unsorted/Contrasimulation html

python scripts/addLinkAnchors.py 

