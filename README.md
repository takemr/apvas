# APVAS
A protocol that reduces the memory consumption of routers running BGPsec when validating AS_PATHs in routing information.
Details of the protocol are described in the following paper.

   https://arxiv.org/abs/2008.13346

# usage
1. Download and install BIRD ver 1.6.0 according to the following site.

   https://bird.network.cz/

1. Download and install TEPLA BIRD ver 2.0 according to the following site.
  
   http://www.cipher.risk.tsukuba.ac.jp/tepla/index.html

1. Replace bird-1.6.0/proto/bgp/packets.c 

1. Run setup.sh

## license

[MIT](https://opensource.org/licenses/mit-license.php)

## Developer

- [takemr](https://github.com/takemr)
- [Naoto Yanai](https://github.com/naotoyanai)
