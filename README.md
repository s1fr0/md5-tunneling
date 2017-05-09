# md5-tunneling
A C implementation of Tunnel Method by V. Klima to speed up collision search for MD5.

## About
Based on Multi-Message Modifications Method and Tunnels, the program searches for two 128-bytes messages with same [MD5](https://en.wikipedia.org/wiki/MD5) hash.

The idea of Tunnels to speed up MD5 collisions search is described in: *Vlastimil Klima: Tunnels in Hash Functions: MD5 Collisions Within a Minute, sent to IACR eprint, 18 March, 2006, [PDF](http://eprint.iacr.org/2006/105.pdf)

## Functionalities
At compile time, the user can choose to
* Enable/disable any implemented tunnel
* Write to disk the two colliding blocks as binaries
* Write to disk a summary of the collision found (the messages' bytes, timings and common hash)
* Print the colliding hash in summary
* Print the colliding hash in standard output

A [Linear Congruential Generator](https://en.wikipedia.org/wiki/Linear_congruential_generator) is implemented as a pseudo-random number generator. The user can set at runtime a seed that produces the same collision across different OS and architectures.

The attack is independent from the Init Vector (IV) used by MD5. The user can set at runtime the IV he wants and search for a collision for that particular IV.

## Compilation
The Math library needs to be linked

```
gcc tunneling.c -lm
```
