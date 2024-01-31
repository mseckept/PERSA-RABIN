︠b52ce453-aec3-482f-84fa-a27a6729b3fd︠
# This worksheet was converted from a notebook running Jupyter kernel
# version sage-10.1.
︡6ac1ffc4-500b-4198-8954-dca36eb8ce57︡{"stdout": "", "done": true}︡
︠c51b055a-f02e-497c-8285-37870cc27033︠
# Usefull functions

def is_cube(a, p): 
    """Test if a is a cubic residue mod p, p prime"""
    return power_mod(a, (p-1)/gcd(3, p-1), p) == 1


def is_square(x, p): 
    """Test if x is a quadratic residue mod p, p prime"""
    return Mod(x, p).is_square()



def rand_prime_congru_1mod3_and_3mod4(size):
    """Randomly generate  a prime p, 2 <= p < 2^size with
       p = 1 mod 3 and p = 3 mod 4
    """
    p = random_prime(2 << size - 1)
    while (p%3 != 1) or (p%4 != 3):
        p = random_prime(2 << size - 1)
    return p


def rand_pq(size):
    """Randomly generate two distinct primes p, q = 1 mod 3"""
    p = rand_prime_congru_1mod3_and_3mod4(size)
    q = p
    while q == p:
        q = rand_prime_congru_1mod3_and_3mod4(size)
    return (p, q)



# Solutions of quadratic equation ax^2+bx+c = 0 mod p^r using Hensel Lemma

def extend_solution_quadratic_equation_mod_pr(coeffs, sol, p, r):
    """Extend a solution *sol* from (mod p) to (mod p^r) of a quadratic equation ax^2+bx+c = 0 
       using Hensel Lemma
    """
    a, b, c = coeffs; x0 = int(sol)
    f = lambda x : a *x^2 + b*x + c
    fprime = lambda x : 2*a*x + b
    # We apply Hensel Lemma
    x0 = int(sol)
    for _ in range(2, r+1):
        x0 = (x0 - f(x0)*inverse_mod(fprime(x0), p^r)) % p^r
    return x0


def solver_quadratic_equation_mod_pr(coeffs, p, r):
    """Solutions of quadratic equation ax^2+bx+c = 0 (mod p^r) using Hensel Lemma"""
    a, b, c = coeffs; assert a%p != 0 and is_square(b^2-4*a*c, p)
    if  p%4 == 3:
        x1 = Mod((-b- power_mod(Mod(b^2-4*a*c, p), (p+1)//4, p)) * inverse_mod(2*a, p), p)
        x2 = Mod((-b + power_mod(Mod(b^2-4*a*c, p), (p+1)//4, p)) * inverse_mod(2*a, p), p)
    else:
        x1 = Mod((-b - Mod(b^2-4*a*c, p).sqrt()) * inverse_mod(2*a, p), p)
        x2 = Mod((-b + Mod(b^2-4*a*c, p).sqrt()) * inverse_mod(2*a, p), p)
        
    x1r = extend_solution_quadratic_equation_mod_pr(coeffs, x1, p, r)
    x2r = extend_solution_quadratic_equation_mod_pr(coeffs, x2, p, r)
    return (x1r, x2r)


def get_sol_with_cubic_pell_point_mod_pr_qs(C, p, q, r, s):
    """Detremine the solution mod p^r and mod q^s given a point on the cubic Pell equation"""
    xc, yc, zc = C; (a, b, c) = zc^3, yc^3-3*xc*yc*zc, xc^3 - 1
    sol_mod_pr = solver_quadratic_equation_mod_pr((a, b, c), p, r)
    sol_mod_qs = solver_quadratic_equation_mod_pr((a, b, c), q, s)
    return (sol_mod_pr, sol_mod_qs)


def is_solution_mod_pr(C, sol, p, r):
    """Test if *sol* is a solution of xc^3 + x*yc^3 + x^2 * zc^3 - 3x*xc*yc*zc = 1 mod p^r"""
    xc, yc, zc = C; (a, b, c) = zc^3, yc^3-3*xc*yc*zc, xc^3 - 1
    f = lambda x : a *x^2 + b*x + c
    return (f(sol) % p^r) == 0


def get_sols_with_ctheo(xp, yq, p, q, r, s):
    """ Determine a solution Y mod N with N=p^rq^s where
    
    Y = xp mod p^r
    Y = yq mod q^s
    """
    N = p^r * q^s
    X = (xp*q^s*inverse_mod(q^s, p^r) + yq*p^r*inverse_mod(p^r, q^s))
    return X % N


def get_possible_a_values(C, p, q, r, s):
    """Determine all values of a such that 
       
       xc^3 + a*yc^3 + a^2 * zc^3 - 3a*xc*yc*zc = 1 mod N with N = p^rq^s
       
    """
    N = p^r * q^s; (xc, yc, zc) = C
    sol_mod_pr, sol_mod_qs = get_sol_with_cubic_pell_point_mod_pr_qs(C, p, q, r, s)
    a1 =  get_sols_with_ctheo(sol_mod_pr[0], sol_mod_qs[0], p, q, r, s)
    a2 =  get_sols_with_ctheo(sol_mod_pr[1], sol_mod_qs[1], p, q, r, s)
    a3 =  get_sols_with_ctheo(sol_mod_pr[0], sol_mod_qs[1], p, q, r, s)
    a4 =  get_sols_with_ctheo(sol_mod_pr[1], sol_mod_qs[0], p, q, r, s)
    possible_a = (a1, a2, a3, a4)
    
    return possible_a


# Arithmetic of cubic pell curve

def add(pt1, pt2, a, N):
    """Add two points pt1 and pt2 on the cubic Pell curve
       C_a(N) = x^3+ay^3+a^2z^3-3axyz =  1 in Z/NZ 
    """
    (x1, y1, z1) =  pt1; (x2, y2, z2) = pt2
    x3 = (x1*x2 + a*(y2*z1 + y1*z2)) % N
    y3 = (x2*y1 + x1*y2 + a*z1*z2) % N
    z3 = (y1*y2 + x2*z1 + x1*z2) % N
    return (x3, y3, z3)


def exponent(pt, e, a, N):
    """Lft to right scalar multiplication on cubic Pell curve
       C_a(N) = x^3+ay^3+a^2z^3-3axyz =  1 in Z/NZ 
    """
    (x1, y1, z1) = pt; (x2, y2, z2) = (1, 0, 0)
    for bit in bin(e)[2:]:
        (x2, y2, z2) = add((x2, y2, z2), (x2, y2, z2), a, N)
        if bit == '1': 
            (x2, y2, z2) = add((x2, y2, z2), (x1, y1, z1), a, N)
    
    return (x2, y2, z2)

            
# Our Scheme 

def keygen(size, r, s):
    """The key generation algorithm
    Parameters:
    - :size: is an integer such that 2 <= p, q < 2^size
    """
    p, q = rand_pq(size)
    N = p^r * q^s
    ordn = p*q*(p^2+p+1)*(q^2+q+1)*(p - 1)^2*(q - 1)^2
    e = randint(1, N)
    while gcd(e, ordn) != 1:
        e = randint(1, N)
        
    d1 = inverse_mod(e, p^(2*(r-1))*q^(2*(s-1))*(p^2+p+1)*(q^2+q+1))
    d2 = inverse_mod(e, p^(2*(r-1))*q^(2*(s-1))*(p - 1)^2*(q - 1)^2)
    d3 = inverse_mod(e, p^(2*(r-1))*q^(2*(s-1))*(p^2+p+1)*(q - 1)^2)
    d4 = inverse_mod(e, p^(2*(r-1))*q^(2*(s-1))*(p - 1)^2*(q^2+q+1))
    return (N, e), (p, q, (r, s), (d1, d2, d3, d4))

    
def encipher(m, pk):
    """Compute the ciphertext of m using the public key pk"""
    (N, e) = pk; (xm, ym) = m
    a = ((1 - xm^3) * inverse_mod(ym^3, N)) % N
    C = exponent((xm, ym, 0), e, a, N)
    return C
    
    
def decipher(ctx, sk):
    """Decipher the ciphertext ctx using the secret key sk"""
    
    (p, q, (r, s), (d1, d2, d3, d4)) = sk
    N =  p^r*q^s
    possible_a = get_possible_a_values(ctx, p, q, r, s)
    for a in possible_a:
        if (not is_cube(a, p)) and (not is_cube(a, q)): 
            d = d1
        elif is_cube(a, p) and is_cube(a, q): 
            d = d2
        elif (not is_cube(a, p)) and is_cube(a, q): 
            d = d3
        else:
            d = d4
        (xm, ym, zm) = exponent(ctx, d, a, N)
        if zm == 0:
            return (xm, ym)
︡a70df537-729c-44f8-bbc5-9a50df255f27︡{"stdout": "", "done": true}︡
︠f206be27-fecd-4bf0-bd6c-1635e170bc7d︠
# Some Tests

r, s = 3, 2
pk, sk = keygen(40, r, s)
N = pk[0]
print("pk = ", pk, "sk = ", sk)
︡fc8b5614-b239-4f4f-a95f-cda43589ebed︡{"html": "<pre><span style=\"font-family:monospace;\">pk =  (69183613403715314293158976471566234696647195621131427425471, 23106690300302391939509400707029121671970426793992711357887) sk =  (965770804519, 277134447787, (3, 2), (1863493589498199108124227352386624487164260810028504221257791573429698621296452596498441611197550586851833735258830077, 4265329590040783123210603376115497248495137676144551411059130572911775393707150455246372385039407051682023196161930223, 2211385035869840099867582309576417035667901622732772419941711953012969236546310414593112475541957690964599580731691875, 2947686423734632693439405339355471360037582565631997855056805585658453660829819000755760789974478388424450877818697811))\n</span></pre>", "done": true}︡
︠46390a62-1aaa-4ff7-b76f-7b6e6cad5c9a︠
number_cipher_text = 10
i = 1
while i<number_cipher_text:
    mi = (randint(0, N), randint(0, N)); print(f"\nmi{i}\t      = {mi}", end="\n")
    ctx = encipher(mi, pk); print(f"ctx{i} = E(mi{i}) = {ctx}", end="\n")
    ptx = decipher(ctx, sk=sk); print(f"ptx{i} = D(ctx{i})= {ptx}")
    i += 1
︡b82d60b4-d863-4c48-aee1-7538aec6590b︡{"html": "<pre><span style=\"font-family:monospace;\">\nmi1\t      = (42643191398808801143705176507784190158672339680513316598435, 59078768134943148026852301058903034935429907062821596667303)\nctx1 = E(mi1) = (16568036415660199479908538528704273586397806052166910395154, 13464238732374805915346687744060912658496465140619153441947, 41601232817169863178085592933282324205119657813461942716339)\nptx1 = D(ctx1)= (42643191398808801143705176507784190158672339680513316598435, 59078768134943148026852301058903034935429907062821596667303)\n\nmi2\t      = (43206035556370981687524394457421930905481396633591233457952, 36677227345271311060203400530360617726438942899442137475483)\nctx2 = E(mi2) = (28163966204012869407145891489806587787603022485790566862832, 55927728631945545417992185099779585097585663352576746798388, 40948898327873233816398165898002970547420587211081511225289)\nptx2 = D(ctx2)= (43206035556370981687524394457421930905481396633591233457952, 36677227345271311060203400530360617726438942899442137475483)\n\nmi3\t      = (11604657898175907850527144491632217307364031985245161443870, 30654355832217309717468150093959581612097421863541237630231)\nctx3 = E(mi3) = (15354879792543011137273526676679443241190186303358783724133, 45851219978436024088093064651412119728819320025128267802636, 9402228817132454737620942378994811008566024996647943727028)\nptx3 = D(ctx3)= (11604657898175907850527144491632217307364031985245161443870, 30654355832217309717468150093959581612097421863541237630231)\n\nmi4\t      = (33413700652994897377174354603209394026073972244978858091651, 66421302643754804568566509819750186441358552646716892436817)\nctx4 = E(mi4) = (63933658695743680732169666364596462648233537066662901088081, 47049531362050124516419163867841034146956440882436973193061, 12935296919392673800888450998660486068861159443715315102875)\nptx4 = D(ctx4)= (33413700652994897377174354603209394026073972244978858091651, 66421302643754804568566509819750186441358552646716892436817)\n\nmi5\t      = (45380094591942602592097148580647089618884182308789219161806, 5840308117198802996519163643016586743756184457834986278825)\nctx5 = E(mi5) = (35870897890922273371763809693941905014404388678770623554617, 12639844472209205204191733340501348808949891119986996332473, 50289809842426550567985440705540602262240979262408549930921)\nptx5 = D(ctx5)= (45380094591942602592097148580647089618884182308789219161806, 5840308117198802996519163643016586743756184457834986278825)\n\nmi6\t      = (36976374723386762092820929167095976607378140272515897678995, 35768731797241610988910995991907783793226262544683249114629)\nctx6 = E(mi6) = (30794681375600398315007210481316180730709094653462644128254, 35723030415688763556602552733388183627490918092166229643635, 11413750834074352906598201063929027211498449559901781954293)\nptx6 = D(ctx6)= (36976374723386762092820929167095976607378140272515897678995, 35768731797241610988910995991907783793226262544683249114629)\n\nmi7\t      = (30576361419474132078615689360194439698812256442361374396262, 28039439516072247840382658968823769641517521659077815942329)\nctx7 = E(mi7) = (47012409196898910259789020271346311854144043335110468002709, 41773982066436316612612399268469681162062034542595465089934, 52846339348229712583424643485699773299821770441362332721464)\nptx7 = D(ctx7)= (30576361419474132078615689360194439698812256442361374396262, 28039439516072247840382658968823769641517521659077815942329)\n\nmi8\t      = (30122499869159545339087331556655029566425681740364148114338, 41304598940541465544956843128695277654710291935810193277397)\nctx8 = E(mi8) = (68403112081373578254451821782073385534262317492288064390988, 55741902304404350880598630911144623299549533355711665027971, 16771169830285946911341267888636174199692713231740603014072)\nptx8 = D(ctx8)= (30122499869159545339087331556655029566425681740364148114338, 41304598940541465544956843128695277654710291935810193277397)\n\nmi9\t      = (12869389784566967996290689615983535648916626633797131491836, 68215058452390359496219667514681791388501149953689358886435)\nctx9 = E(mi9) = (63823671028903030547958160785208647118284084649181017980329, 64726571255456748754751555062574306326165735950661067641410, 20198787864996527417775979969762533817841252026819159278017)\nptx9 = D(ctx9)= (12869389784566967996290689615983535648916626633797131491836, 68215058452390359496219667514681791388501149953689358886435)\n</span></pre>", "done": true}︡
