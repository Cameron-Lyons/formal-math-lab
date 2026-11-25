/* Narrow raw-file gate for the dedicated checked byte-exponent executable.
 * Accepted syntax uses x1,...,xn headers and expanded integer monomials.
 * This rejects malformed tokens before upstream strtol/int32 conversions. */
#ifndef MSOLVE_BYTE_INPUT_GUARD_H
#define MSOLVE_BYTE_INPUT_GUARD_H
static void byte_input_error(const char *why)
{
    fprintf(stderr,"Error: byte input guard: %s.\n",why);
    exit(EXIT_FAILURE);
}
[[maybe_unused]] static uint32_t byte_cli_integer(const char *s)
{
    if (s==NULL || !*s) byte_input_error("missing numeric option");
    uint32_t n=0;
    for (;*s;s++) {
        if (*s<'0'||*s>'9') byte_input_error("noncanonical numeric option");
        const uint32_t d=(uint32_t)(*s-'0');
        if (n>((uint32_t)INT32_MAX-d)/10) byte_input_error("numeric option overflow");
        n=10*n+d;
    }
    return n;
}
static void byte_next(FILE *f,int *ch) { *ch=fgetc(f); }
static void byte_space(FILE *f,int *ch)
{
    while (*ch!=EOF && isspace((unsigned char)*ch)) byte_next(f,ch);
}
static uint32_t byte_number(FILE *f,int *ch,const uint32_t limit)
{
    if (*ch<'0'||*ch>'9') byte_input_error("expected unsigned decimal integer");
    uint32_t n=0;
    do {
        const uint32_t d=(uint32_t)(*ch-'0');
        if (d>limit || n>(limit-d)/10) byte_input_error("numeric token overflow");
        n=10*n+d;byte_next(f,ch);
    } while (*ch>='0'&&*ch<='9');
    return n;
}
static void byte_validate_file(const char *path)
{
    FILE *f=fopen(path,"r");
    if (!f) byte_input_error("cannot open input");
    char line[2048];
    if (!fgets(line,sizeof(line),f) || !strchr(line,'\n'))
        byte_input_error("unsupported variable header");
    char *at=line;uint32_t nv=0;
    while (1) {
        char expected[16];
        if (++nv>127) byte_input_error("variable count exceeds127");
        snprintf(expected,sizeof(expected),"x%u",nv);
        const size_t k=strlen(expected);
        if (strncmp(at,expected,k)) byte_input_error("header must be x1 through xn");
        at+=k;
        if (*at==',') {at++;continue;}
        if (*at=='\r') at++;
        if (*at!='\n'||at[1]!=0) byte_input_error("bad variable header suffix");
        break;
    }
    if (!fgets(line,sizeof(line),f) || (strcmp(line,"3\n") && strcmp(line,"3\r\n")))
        byte_input_error("only characteristic3 is supported");
    int ch=fgetc(f);byte_space(f,&ch);
    uint32_t terms=0,polys=0;
    while (ch!=EOF) {
        if (++polys>1000000) byte_input_error("too many polynomials");
        if (ch=='+'||ch=='-') byte_next(f,&ch);
        while (1) {
            if (++terms>10000000) byte_input_error("too many terms");
            uint8_t seen[127]={0};int has_coefficient=0;
            if (ch>='0'&&ch<='9') {
                (void)byte_number(f,&ch,INT32_MAX);has_coefficient=1;
                if (ch=='*') {byte_next(f,&ch);if(ch!='x')byte_input_error("coefficient must precede variables");}
                else if (ch=='x') byte_input_error("missing multiplication sign");
            }
            if (ch=='x') {
                while (1) {
                    byte_next(f,&ch);
                    if (ch=='0') byte_input_error("noncanonical variable index");
                    const uint32_t v=byte_number(f,&ch,nv);
                    if (v<1 || seen[v-1]) byte_input_error("unknown or repeated variable factor");
                    seen[v-1]=1;
                    if (ch=='^') {byte_next(f,&ch);(void)byte_number(f,&ch,UINT8_MAX);}
                    if (ch!='*') break;
                    byte_next(f,&ch);
                    if (ch!='x') byte_input_error("expected variable after multiplication");
                }
            } else if (!has_coefficient) byte_input_error("expected monomial");
            byte_space(f,&ch);
            if (ch=='+'||ch=='-') {byte_next(f,&ch);continue;}
            if (ch==',') {
                byte_next(f,&ch);byte_space(f,&ch);
                if(ch==EOF)byte_input_error("trailing polynomial separator");
                break;
            }
            if (ch==EOF) break;
            byte_input_error("unsupported polynomial syntax");
        }
    }
    if (!polys || ferror(f)) byte_input_error("empty or unreadable polynomial body");
    fclose(f);
}
#endif
