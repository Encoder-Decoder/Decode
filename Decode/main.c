#include <math.h>
#include <stdio.h>
#define mm  4           /* RS code over GF(2**4) - change to suit:(x^0 x^1 x^2 x^3 x^4 -> 2^4 =x^4 +x+1=11001)*/
#define nn  15          /* nn=2**mm -1   length of codeword  */
#define tt  3           /* number of errors that can be corrected */
#define kk  9           /* kk = nn-2*tt  */


int alpha_to[nn + 1], index_of[nn + 1], gg[nn - kk + 1];
int recd[nn], data[kk + 2 + kk], bb[nn - kk], dataSave[kk];
int saveIndexPading = 0, lenght = 0, orginal[kk + 2 + kk],  t;
int index = 0, countChank=0, indexC=0;

void decode_rs()

{
    register int i, j, u, q;
    int elp[nn - kk + 2][nn - kk], d[nn - kk + 2], l[nn - kk + 2], u_lu[nn - kk + 2], s[nn - kk + 1];
    int count = 0, syn_error = 0, root[tt], loc[tt], z[tt + 1], err[nn], reg[tt + 1];

    /* first form the syndromes */
    for (i = 1; i <= nn - kk; i++)
    {
        s[i] = 0;
        for (j = 0; j < nn; j++)
            if (recd[j] != -1)
                s[i] ^= alpha_to[(recd[j] + i * j) % nn];      /* recd[j] in index form */
      /* convert syndrome from polynomial form to index form  */
        if (s[i] != 0)  syn_error = 1;        /* set flag if non-zero syndrome => error */
        s[i] = index_of[s[i]];
    };

    if (syn_error)       /* if errors, try and correct */
    {
        /* compute the error location polynomial via the Berlekamp iterative algorithm,
           following the terminology of Lin and Costello :   d[u] is the 'mu'th
           discrepancy, where u='mu'+1 and 'mu' (the Greek letter!) is the step number
           ranging from -1 to 2*tt (see L&C),  l[u] is the
           degree of the elp at that step, and u_l[u] is the difference between the
           step number and the degree of the elp.
        */
        /* initialise table entries */
        d[0] = 0;           /* index form */
        d[1] = s[1];        /* index form */
        elp[0][0] = 0;      /* index form */
        elp[1][0] = 1;      /* polynomial form */
        for (i = 1; i < nn - kk; i++)
        {
            elp[0][i] = -1;   /* index form */
            elp[1][i] = 0;   /* polynomial form */
        }
        l[0] = 0;
        l[1] = 0;
        u_lu[0] = -1;
        u_lu[1] = 0;
        u = 0;

        do
        {
            u++;
            if (d[u] == -1)
            {
                l[u + 1] = l[u];
                for (i = 0; i <= l[u]; i++)
                {
                    elp[u + 1][i] = elp[u][i];
                    elp[u][i] = index_of[elp[u][i]];
                }
            }
            else
                /* search for words with greatest u_lu[q] for which d[q]!=0 */
            {
                q = u - 1;
                while ((d[q] == -1) && (q > 0)) q--;
                /* have found first non-zero d[q]  */
                if (q > 0)
                {
                    j = q;
                    do
                    {
                        j--;
                        if ((d[j] != -1) && (u_lu[q] < u_lu[j]))
                            q = j;
                    } while (j > 0);
                };

                /* have now found q such that d[u]!=0 and u_lu[q] is maximum */
                /* store degree of new elp polynomial */
                if (l[u] > l[q] + u - q)  l[u + 1] = l[u];
                else  l[u + 1] = l[q] + u - q;

                /* form new elp(x) */
                for (i = 0; i < nn - kk; i++)    elp[u + 1][i] = 0;
                for (i = 0; i <= l[q]; i++)
                    if (elp[q][i] != -1)
                        elp[u + 1][i + u - q] = alpha_to[(d[u] + nn - d[q] + elp[q][i]) % nn];
                for (i = 0; i <= l[u]; i++)
                {
                    elp[u + 1][i] ^= elp[u][i];
                    elp[u][i] = index_of[elp[u][i]];  /*convert old elp value to index*/
                }
            }
            u_lu[u + 1] = u - l[u + 1];

            /* form (u+1)th discrepancy */
            if (u < nn - kk)    /* no discrepancy computed on last iteration */
            {
                if (s[u + 1] != -1)
                    d[u + 1] = alpha_to[s[u + 1]];
                else
                    d[u + 1] = 0;
                for (i = 1; i <= l[u + 1]; i++)
                    if ((s[u + 1 - i] != -1) && (elp[u + 1][i] != 0))
                        d[u + 1] ^= alpha_to[(s[u + 1 - i] + index_of[elp[u + 1][i]]) % nn];
                d[u + 1] = index_of[d[u + 1]];    /* put d[u+1] into index form */
            }
        } while ((u < nn - kk) && (l[u + 1] <= tt));

        u++;
        if (l[u] <= tt)         /* can correct error */
        {
            /* put elp into index form */
            for (i = 0; i <= l[u]; i++)   elp[u][i] = index_of[elp[u][i]];

            /* find roots of the error location polynomial */
            for (i = 1; i <= l[u]; i++)
                reg[i] = elp[u][i];
            count = 0;
            for (i = 1; i <= nn; i++)
            {
                q = 1;
                for (j = 1; j <= l[u]; j++)
                    if (reg[j] != -1)
                    {
                        reg[j] = (reg[j] + j) % nn;
                        q ^= alpha_to[reg[j]];
                    };
                if (!q)        /* store root and error location number indices */
                {
                    root[count] = i;
                    loc[count] = nn - i;
                    count++;
                };
            };
            if (count == l[u])    /* no. roots = degree of elp hence <= tt errors */
            {
                /* form polynomial z(x) */
                for (i = 1; i <= l[u]; i++)        /* Z[0] = 1 always - do not need */
                {
                    if ((s[i] != -1) && (elp[u][i] != -1))
                        z[i] = alpha_to[s[i]] ^ alpha_to[elp[u][i]];
                    else if ((s[i] != -1) && (elp[u][i] == -1))
                        z[i] = alpha_to[s[i]];
                    else if ((s[i] == -1) && (elp[u][i] != -1))
                        z[i] = alpha_to[elp[u][i]];
                    else
                        z[i] = 0;
                    for (j = 1; j < i; j++)
                        if ((s[j] != -1) && (elp[u][i - j] != -1))
                            z[i] ^= alpha_to[(elp[u][i - j] + s[j]) % nn];
                    z[i] = index_of[z[i]];         /* put into index form */
                };

                /* evaluate errors at locations given by error location numbers loc[i] */
                for (i = 0; i < nn; i++)
                {
                    err[i] = 0;
                    if (recd[i] != -1)        /* convert recd[] to polynomial form */
                        recd[i] = alpha_to[recd[i]];
                    else  recd[i] = 0;
                }
                for (i = 0; i < l[u]; i++)    /* compute numerator of error term first */
                {
                    err[loc[i]] = 1;       /* accounts for z[0] */
                    for (j = 1; j <= l[u]; j++)
                        if (z[j] != -1)
                            err[loc[i]] ^= alpha_to[(z[j] + j * root[i]) % nn];
                    if (err[loc[i]] != 0)
                    {
                        err[loc[i]] = index_of[err[loc[i]]];
                        q = 0;     /* form denominator of error term */
                        for (j = 0; j < l[u]; j++)
                            if (j != i)
                                q += index_of[1 ^ alpha_to[(loc[j] + root[i]) % nn]];
                        q = q % nn;
                        err[loc[i]] = alpha_to[(err[loc[i]] - q + nn) % nn];
                        recd[loc[i]] ^= err[loc[i]];  /*recd[i] must be in polynomial form */
                    }
                }
            }
            else    /* no. roots != degree of elp => >tt errors and cannot solve */
                for (i = 0; i < nn; i++)        /* could return error flag if desired */
                    if (recd[i] != -1)        /* convert recd[] to polynomial form */
                        recd[i] = alpha_to[recd[i]];
                    else  recd[i] = 0;     /* just output received codeword as is */
        }
        else         /* elp has degree has degree >tt hence cannot solve */
            for (i = 0; i < nn; i++)       /* could return error flag if desired */
                if (recd[i] != -1)        /* convert recd[] to polynomial form */
                    recd[i] = alpha_to[recd[i]];
                else  recd[i] = 0;     /* just output received codeword as is */
    }
    else       /* no non-zero syndromes => no errors: output received codeword */
        for (i = 0; i < nn; i++)
            if (recd[i] != -1)        /* convert recd[] to polynomial form */
                recd[i] = alpha_to[recd[i]];
            else  recd[i] = 0;
}

void readNumOfAllChunks() {

    FILE* fpi;

    fopen_s(&fpi, "numOfAllChunks.bin", "rb");
    fread(&countChank, sizeof(int), 1, fpi);

    fclose(fpi);
}

void readArrGenerate_gf() {
    FILE* fp;
    int i = 0;

    fopen_s(&fp, "ArrGenerate.bin", "rb");
    printf("\n We read these arr for Decode: \n");
    printf("\nindex_of:\n ");
    for (i = 0; i < nn + 1; i++)
    {
        fread(&index_of[i], sizeof(int), 1, fp);
        printf("%d ", index_of[i]);
    }

    printf("\nalpha_to:\n ");
    for (i = 0; i < nn + 1; i++)
    {
        fread(&alpha_to[i], sizeof(int), 1, fp);
        printf("%d ", alpha_to[i]);

    }

    printf("\ngg:\n ");
    for (i = 0; i < nn - kk + 1; i++)
    {
        fread(&gg[i], sizeof(int), 1, fp);
        printf("%d ", gg[i]);
    }
    fclose(fp);

}

void readDataAfterChange(int indexC)
{
    FILE* fp;
    fopen_s(&fp, "afterChange.bin", "rb");

    if (indexC == 0)
    {
        fseek(fp, 0, SEEK_CUR);
        printf("\nShank number: %d\n", 0);
        printf("\n read data after change from bin file:\n");
        for (int i = 0; i < nn; i++)
        {
            fread(&recd[i], sizeof(int), 1, fp);
            printf("%d ", recd[i]);
        }
    }
    else {
        fseek(fp, (4 * 15 * indexC), SEEK_CUR);
        printf("\n\nShank number: %d\n",indexC);
        printf("\n read data after change from bin file:\n");
        for (int i = 0; i < nn; i++)
        {
            fread(&recd[i], sizeof(int), 1, fp);
            printf("%d ", recd[i]);
        }


    }
    fclose(fp);
}

void deleteBinFile() {

    if (remove("OrginalData.bin") == 0) {
        printf("The file is deleted successfully.");
    }
    else {
        printf("The file is not deleted.");
    }

    if (remove("IndexPading.bin") == 0) {
        printf("The file is deleted successfully.");
    }
    else {
        printf("The file is not deleted.");
    }

    if (remove("afterChange.bin") == 0) {
        printf("The file is deleted successfully.");
    }
    else {
        printf("The file is not deleted.");
    }

}

void divideData() {

    readNumOfAllChunks();
    readArrGenerate_gf();
    
    printf("\n\ncount chanks: %d \n", countChank);
   
    for (int i = 1; i <= countChank; i++)
    {
       
      readDataAfterChange(indexC);
      printf("\n Data after change before decode:\n");
      for (int i = 0; i < nn; i++)
        {
            printf("%d ", recd[i]);
        }
        for (int i= 0; i <nn; i++)
            recd[i] = index_of[recd[i]];
       
        decode_rs();
        printf("\nData after decoder\n");
        for (int i = 0; i < nn; i++)
        {
            printf("%d ", recd[i]);
        }
        printf("\n");
        indexC++;
    }
}


int main()
{
    divideData();
}