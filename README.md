# md5-tunneling
A C implementation of Tunnel Method by V. Klima to speed up collision search for MD5.

## About
Based on Multi-Message Modifications Method and Tunnels, the program searches for two 128-bytes messages with same [MD5](https://en.wikipedia.org/wiki/MD5) hash.

The idea of Tunnels to speed up MD5 collisions search is described in: *Vlastimil Klima: Tunnels in Hash Functions: MD5 Collisions Within a Minute, sent to IACR eprint, 18 March, 2006* [PDF](http://eprint.iacr.org/2006/105.pdf)


## Compilation
The Math library needs to be linked

```
gcc tunneling.c -lm -o md5-tunneling
```

## Functionalities
At compile time, the user can choose to
* Enable/disable any implemented tunnel
* Write to disk the two colliding messages as binaries
* Write to disk a summary of the collision found (messages' bytes, timings and common hash)
* Print the colliding hash in summary
* Print the colliding hash in standard output

A [Linear Congruential Generator](https://en.wikipedia.org/wiki/Linear_congruential_generator) is implemented as a pseudo-random number generator. The user can set a seed that produces the same collision across different OS and architectures.

The attack is independent from the Init Vector (IV) used by MD5. The user can set the IV he wants and search for a collision for that particular IV.

You can give as input to the program:
* 1 hex number to specify the seed
```
md5-tunneling 0x69423840
```
* 4 hex numbers to specify the custom IV for MD5
```
md5-tunneling 0xF0E1D2C3 0xB4A59687 0x78695A4B 0x3C2D1E0F
```
* 5 hex numbers to specify the seed and custom IV
```
md5-tunneling 0x69423840 0xF0E1D2C3 0xB4A59687 0x78695A4B 0x3C2D1E0F
```
