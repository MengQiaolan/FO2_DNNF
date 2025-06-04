## Install
```bash
pip install git+https://github.com/yuanhong-wang/WFOMC
```

## Directly build DNNF from FO2:
```bash
# example
python compiler.py -i sentence/nonisolated/nonisolated.wfomcs -n 3
```
```bash
python compiler.py -i INPUT -n DOMAIN_SIZE

# options:
#  -i INPUT              sentence file
#  -n DOMAIN_SIZE        domain size
```

## Convert FO2 to CNF first, and build wDNNF:

```bash
# example
python fo2cnf.py -i sentence/nonisolated/nonisolated.wfomcs -s -n 3
```

```bash
python fo2cnf.py -i INPUT [--show] -n DOMAIN_SIZE

# options:
#  -i INPUT              sentence file
#  -n DOMAIN_SIZE        domain size
#  -show -s              show the circuit
```

