#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

int             m = 6, n = 63, length = 63, k = 16, t = 11, d = 23;
int             p[7];
int             alpha_to[64], index_of[64], g[48];
int             recd[64], data[16], bb[48];
int             numerr, errpos[64], decerror = 0;

void  read_p(){
    p[0] = p[1] = p[6] = 1;
    p[2] = p[3] = p[4] = p[5] = 0;
}

void generate_gf(){
	register int    i, mask;

	mask = 1;
	alpha_to[m] = 0;
	for (i = 0; i < m; i++) {
		alpha_to[i] = mask;
		index_of[alpha_to[i]] = i;
		if (p[i] != 0)
			alpha_to[m] ^= mask;
		mask <<= 1;
	}
	index_of[alpha_to[m]] = m;
	mask >>= 1;
	for (i = m + 1; i < n; i++) {
		if (alpha_to[i - 1] >= mask)
		  alpha_to[i] = alpha_to[m] ^ ((alpha_to[i - 1] ^ mask) << 1);
		else
		  alpha_to[i] = alpha_to[i - 1] << 1;
		index_of[alpha_to[i]] = i;
	}
	index_of[0] = -1;
}

void gen_poly(){
    for(int i = 0; i<=length-k; i++)
        g[i] = 1;

    g[ 2] = g[ 4] = g[ 6] = g[ 7] = g[10] = g[14] = 0;
    g[15] = g[17] = g[21] = g[26] = g[28] = g[29] = 0;
    g[30] = g[31] = g[34] = g[35] = g[37] = g[38] = 0;
    g[41] = g[44] = g[45] = 0;

    printf("\ng(x) = ");
    for(int i = 0; i<=length-k; i++)
        printf("%d",g[i]);
    printf("\n");

}

void encode_bch(){

	register int    i, j;
	register int    feedback;

	for (i = 0; i < length - k; i++)
		bb[i] = 0;
	for (i = k - 1; i >= 0; i--) {
		feedback = data[i] ^ bb[length - k - 1];
		if (feedback != 0) {
			for (j = length - k - 1; j > 0; j--)
				if (g[j] != 0)
					bb[j] = bb[j - 1] ^ feedback;
				else
					bb[j] = bb[j - 1];
			bb[0] = g[0] && feedback;
		} else {
			for (j = length - k - 1; j > 0; j--)
				bb[j] = bb[j - 1];
			bb[0] = 0;
		};
	};
};


void decode_bch(){
    register int    i, j, u, q, t2, count = 0, syn_error = 0;
	int             elp[1026][1024], d[1026], l[1026], u_lu[1026], s[1025];
	int             root[200], loc[200], err[1024], reg[201];

	t2 = 2 * t;

	/* first form the syndromes */
	printf("S(x) = ");
	for (i = 1; i <= t2; i++) {
		s[i] = 0;
		for (j = 0; j < length; j++)
			if (recd[j] != 0)
				s[i] ^= alpha_to[(i * j) % n];
		if (s[i] != 0)
			syn_error = 1; /* set error flag if non-zero syndrome */
/*
 * Note:    If the code is used only for ERROR DETECTION, then
 *          exit program here indicating the presence of errors.
 */
		/* convert syndrome from polynomial form to index form  */
		s[i] = index_of[s[i]];
		printf("%3d ", s[i]);
	}
	printf("\n");

	if (syn_error) {

		d[0] = 0;			/* index form */
		d[1] = s[1];		/* index form */
		elp[0][0] = 0;		/* index form */
		elp[1][0] = 1;		/* polynomial form */
		for (i = 1; i < t2; i++) {
			elp[0][i] = -1;	/* index form */
			elp[1][i] = 0;	/* polynomial form */
		}
		l[0] = 0;
		l[1] = 0;
		u_lu[0] = -1;
		u_lu[1] = 0;
		u = 0;

		do {
			u++;
			if (d[u] == -1) {
				l[u + 1] = l[u];
				for (i = 0; i <= l[u]; i++) {
					elp[u + 1][i] = elp[u][i];
					elp[u][i] = index_of[elp[u][i]];
				}
			} else
				/*
				 * search for words with greatest u_lu[q] for
				 * which d[q]!=0
				 */
			{
				q = u - 1;
				while ((d[q] == -1) && (q > 0))
					q--;
				/* have found first non-zero d[q]  */
				if (q > 0) {
				  j = q;
				  do {
				    j--;
				    if ((d[j] != -1) && (u_lu[q] < u_lu[j]))
				      q = j;
				  } while (j > 0);
				}

				/*
				 * have now found q such that d[u]!=0 and
				 * u_lu[q] is maximum
				 */
				/* store degree of new elp polynomial */
				if (l[u] > l[q] + u - q)
					l[u + 1] = l[u];
				else
					l[u + 1] = l[q] + u - q;

				/* form new elp(x) */
				for (i = 0; i < t2; i++)
					elp[u + 1][i] = 0;
				for (i = 0; i <= l[q]; i++)
					if (elp[q][i] != -1)
						elp[u + 1][i + u - q] =
                                   alpha_to[(d[u] + n - d[q] + elp[q][i]) % n];
				for (i = 0; i <= l[u]; i++) {
					elp[u + 1][i] ^= elp[u][i];
					elp[u][i] = index_of[elp[u][i]];
				}
			}
			u_lu[u + 1] = u - l[u + 1];

			/* form (u+1)th discrepancy */
			if (u < t2) {
			/* no discrepancy computed on last iteration */
			  if (s[u + 1] != -1)
			    d[u + 1] = alpha_to[s[u + 1]];
			  else
			    d[u + 1] = 0;
			    for (i = 1; i <= l[u + 1]; i++)
			      if ((s[u + 1 - i] != -1) && (elp[u + 1][i] != 0))
			        d[u + 1] ^= alpha_to[(s[u + 1 - i]
			                      + index_of[elp[u + 1][i]]) % n];
			  /* put d[u+1] into index form */
			  d[u + 1] = index_of[d[u + 1]];
			}
		} while ((u < t2) && (l[u + 1] <= t));

		u++;
		if (l[u] <= t) {/* Can correct errors */
			/* put elp into index form */
			for (i = 0; i <= l[u]; i++)
				elp[u][i] = index_of[elp[u][i]];

			printf("sigma(x) = ");
			for (i = 0; i <= l[u]; i++)
				printf("%3d ", elp[u][i]);
			printf("\n");
			printf("Roots: ");

			/* Chien search: find roots of the error location polynomial */
			for (i = 1; i <= l[u]; i++)
				reg[i] = elp[u][i];
			count = 0;
			for (i = 1; i <= n; i++) {
				q = 1;
				for (j = 1; j <= l[u]; j++)
					if (reg[j] != -1) {
						reg[j] = (reg[j] + j) % n;
						q ^= alpha_to[reg[j]];
					}
				if (!q) {	/* store root and error
						 * location number indices */
					root[count] = i;
					loc[count] = n - i;
					count++;
					printf("%3d ", n - i);
				}
			}
			printf("\n");
			if (count == l[u])
			/* no. roots = degree of elp hence <= t errors */
				for (i = 0; i < l[u]; i++)
					recd[loc[i]] ^= 1;
			else	/* elp has degree >t hence cannot solve */
				printf("Incomplete decoding: errors detected\n");
		}
	}
}

int main() {
	int i;

	printf("This is a (%d, %d, %d) binary BCH code\n", length, k, d);

	read_p();               /* Read m */
	generate_gf();
	gen_poly();				/* Compute the generator polynomial of BCH code */

	for (i = 0; i < k; i++)
        data[i] = 0;

    for (i = 0; i < k; i=i+2)
        data[i] = 1;

	/* ENCODE */
	encode_bch();			/* encode data */

	for (i = 0; i < length - k; i++)
		recd[i] = bb[i];	/* first (length-k) bits are redundancy */
	for (i = 0; i < k; i++)
		recd[i + length - k] = data[i];	/* last k bits are data */
	printf("c(x) = ");
	for (i = 0; i < length; i++) {
		printf("%1d", recd[i]);
		if (i && ((i % 50) == 0))
			printf("\n");
	}
	printf("\n");

	/* ERRORS */
	srand(time(NULL));

	do{
        numerr = rand() % length;
	}while (numerr > t);

    printf("Number of errors: %d \n", numerr);

    if (numerr == 0)
        printf("No error \n");
    else{
        for (i=0; i < numerr; i++){
            errpos[i] = rand() % length;
        }
    }
    printf("\n");

	for (i = 0; i < numerr; i++){
        recd[errpos[i]] ^= 1;
    }
	printf("r(x) = ");
	for (i = 0; i < length; i++)
		printf("%1d", recd[i]);
	printf("\n");

    /* DECODE */
	decode_bch();

	printf("Results:\n");
	printf("original data  = ");
	for (i = 0; i < k; i++)
		printf("%1d", data[i]);

	printf("\nrecovered data = ");
	for (i = length - k; i < length; i++)
		printf("%1d", recd[i]);
	printf("\n");

	/* decoding errors: we compare only the data portion */
	for (i = length - k; i < length; i++)
		if (data[i - length + k] != recd[i])
			decerror++;
	if (decerror)
		printf("%d message decoding errors\n", decerror);
	else
		printf("Successful decoding\n");
}
