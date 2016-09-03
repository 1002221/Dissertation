# Dissertation

This folder contains a proof with VCC (a deductive verifier) that s2n (an implementation of the TLS security protocol) correctly implements the HMAC construction. Moreover, this proof includes showing that the code is free from errors such as memory errors and arithmetic overﬂows. Our proof has revealed an error in the (s2n_hmac_digest_two_compression_rounds), which turned out to not be a bug in the current implementation but which could have been a bug in a diﬀerent one.

For relevant papers and installation instructions for VCC, please visit https://vcc.codeplex.com .

To run this proof, open all the files into a project and verify s2n_hmac.c .



