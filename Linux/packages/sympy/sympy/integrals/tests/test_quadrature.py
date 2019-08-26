from sympy.core import S
from sympy.integrals.quadrature import (gauss_legendre, gauss_laguerre,
                                        gauss_hermite, gauss_gen_laguerre,
                                        gauss_chebyshev_t, gauss_chebyshev_u,
                                        gauss_jacobi, gauss_lobatto)


def test_legendre():
    x, w = gauss_legendre(1, 17)
    assert [str(r) for r in x] == ['0']
    assert [str(r) for r in w] == ['2.0000000000000000']

    x, w = gauss_legendre(2, 17)
    assert [str(r) for r in x] == [
            '-0.57735026918962576',
            '0.57735026918962576']
    assert [str(r) for r in w] == [
            '1.0000000000000000',
            '1.0000000000000000']

    x, w = gauss_legendre(3, 17)
    assert [str(r) for r in x] == [
            '-0.77459666924148338',
            '0',
            '0.77459666924148338']
    assert [str(r) for r in w] == [
            '0.55555555555555556',
            '0.88888888888888889',
            '0.55555555555555556']

    x, w = gauss_legendre(4, 17)
    assert [str(r) for r in x] == [
            '-0.86113631159405258',
            '-0.33998104358485626',
            '0.33998104358485626',
            '0.86113631159405258']
    assert [str(r) for r in w] == [
            '0.34785484513745386',
            '0.65214515486254614',
            '0.65214515486254614',
            '0.34785484513745386']


def test_legendre_precise():
    x, w = gauss_legendre(3, 40)
    assert [str(r) for r in x] == [
            '-0.7745966692414833770358530799564799221666',
            '0',
            '0.7745966692414833770358530799564799221666']
    assert [str(r) for r in w] == [
            '0.5555555555555555555555555555555555555556',
            '0.8888888888888888888888888888888888888889',
            '0.5555555555555555555555555555555555555556']


def test_laguerre():
    x, w = gauss_laguerre(1, 17)
    assert [str(r) for r in x] == ['1.0000000000000000']
    assert [str(r) for r in w] == ['1.0000000000000000']

    x, w = gauss_laguerre(2, 17)
    assert [str(r) for r in x] == [
            '0.58578643762690495',
            '3.4142135623730950']
    assert [str(r) for r in w] == [
            '0.85355339059327376',
            '0.14644660940672624']

    x, w = gauss_laguerre(3, 17)
    assert [str(r) for r in x] == [
            '0.41577455678347908',
            '2.2942803602790417',
            '6.2899450829374792',
            ]
    assert [str(r) for r in w] == [
            '0.71109300992917302',
            '0.27851773356924085',
            '0.010389256501586136',
            ]

    x, w = gauss_laguerre(4, 17)
    assert [str(r) for r in x] == [
            '0.32254768961939231',
            '1.7457611011583466',
            '4.5366202969211280',
            '9.3950709123011331']
    assert [str(r) for r in w] == [
            '0.60315410434163360',
            '0.35741869243779969',
            '0.038887908515005384',
            '0.00053929470556132745']

    x, w = gauss_laguerre(5, 17)
    assert [str(r) for r in x] == [
            '0.26356031971814091',
            '1.4134030591065168',
            '3.5964257710407221',
            '7.0858100058588376',
            '12.640800844275783']
    assert [str(r) for r in w] == [
            '0.52175561058280865',
            '0.39866681108317593',
            '0.075942449681707595',
            '0.0036117586799220485',
            '2.3369972385776228e-5']


def test_laguerre_precise():
    x, w = gauss_laguerre(3, 40)
    assert [str(r) for r in x] == [
            '0.4157745567834790833115338731282744735466',
            '2.294280360279041719822050361359593868960',
            '6.289945082937479196866415765512131657493']
    assert [str(r) for r in w] == [
            '0.7110930099291730154495901911425944313094',
            '0.2785177335692408488014448884567264810349',
            '0.01038925650158613574896492040067908765572']


def test_hermite():
    x, w = gauss_hermite(1, 17)
    assert [str(r) for r in x] == ['0']
    assert [str(r) for r in w] == ['1.7724538509055160']

    x, w = gauss_hermite(2, 17)
    assert [str(r) for r in x] == [
            '-0.70710678118654752',
            '0.70710678118654752']
    assert [str(r) for r in w] == [
            '0.88622692545275801',
            '0.88622692545275801']

    x, w = gauss_hermite(3, 17)
    assert [str(r) for r in x] == [
            '-1.2247448713915890',
            '0',
            '1.2247448713915890']
    assert [str(r) for r in w] == [
            '0.29540897515091934',
            '1.1816359006036774',
            '0.29540897515091934']

    x, w = gauss_hermite(4, 17)
    assert [str(r) for r in x] == [
            '-1.6506801238857846',
            '-0.52464762327529032',
            '0.52464762327529032',
            '1.6506801238857846']
    assert [str(r) for r in w] == [
            '0.081312835447245177',
            '0.80491409000551284',
            '0.80491409000551284',
            '0.081312835447245177']

    x, w = gauss_hermite(5, 17)
    assert [str(r) for r in x] == [
            '-2.0201828704560856',
            '-0.95857246461381851',
            '0',
            '0.95857246461381851',
            '2.0201828704560856']
    assert [str(r) for r in w] == [
            '0.019953242059045913',
            '0.39361932315224116',
            '0.94530872048294188',
            '0.39361932315224116',
            '0.019953242059045913']


def test_hermite_precise():
    x, w = gauss_hermite(3, 40)
    assert [str(r) for r in x] == [
        '-1.224744871391589049098642037352945695983',
        '0',
        '1.224744871391589049098642037352945695983']
    assert [str(r) for r in w] == [
        '0.2954089751509193378830279138901908637996',
        '1.181635900603677351532111655560763455198',
        '0.2954089751509193378830279138901908637996']


def test_gen_laguerre():
    x, w = gauss_gen_laguerre(1, -S.Half, 17)
    assert [str(r) for r in x] == ['0.50000000000000000']
    assert [str(r) for r in w] == ['1.7724538509055160']

    x, w = gauss_gen_laguerre(2, -S.Half, 17)
    assert [str(r) for r in x] == [
            '0.27525512860841095',
            '2.7247448713915890']
    assert [str(r) for r in w] == [
            '1.6098281800110257',
            '0.16262567089449035']

    x, w = gauss_gen_laguerre(3, -S.Half, 17)
    assert [str(r) for r in x] == [
            '0.19016350919348813',
            '1.7844927485432516',
            '5.5253437422632603']
    assert [str(r) for r in w] == [
            '1.4492591904487850',
            '0.31413464064571329',
            '0.0090600198110176913']

    x, w = gauss_gen_laguerre(4, -S.Half, 17)
    assert [str(r) for r in x] == [
            '0.14530352150331709',
            '1.3390972881263614',
            '3.9269635013582872',
            '8.5886356890120343']
    assert [str(r) for r in w] == [
            '1.3222940251164826',
            '0.41560465162978376',
            '0.034155966014826951',
            '0.00039920814442273524']

    x, w = gauss_gen_laguerre(5, -S.Half, 17)
    assert [str(r) for r in x] == [
            '0.11758132021177814',
            '1.0745620124369040',
            '3.0859374437175500',
            '6.4147297336620305',
            '11.807189489971737']
    assert [str(r) for r in w] == [
            '1.2217252674706516',
            '0.48027722216462937',
            '0.067748788910962126',
            '0.0026872914935624654',
            '1.5280865710465241e-5']

    x, w = gauss_gen_laguerre(1, 2, 17)
    assert [str(r) for r in x] == ['3.0000000000000000']
    assert [str(r) for r in w] == ['2.0000000000000000']

    x, w = gauss_gen_laguerre(2, 2, 17)
    assert [str(r) for r in x] == [
            '2.0000000000000000',
            '6.0000000000000000']
    assert [str(r) for r in w] == [
            '1.5000000000000000',
            '0.50000000000000000']

    x, w = gauss_gen_laguerre(3, 2, 17)
    assert [str(r) for r in x] == [
            '1.5173870806774125',
            '4.3115831337195203',
            '9.1710297856030672']
    assert [str(r) for r in w] == [
            '1.0374949614904253',
            '0.90575000470306537',
            '0.056755033806509347']

    x, w = gauss_gen_laguerre(4, 2, 17)
    assert [str(r) for r in x] == [
            '1.2267632635003021',
            '3.4125073586969460',
            '6.9026926058516134',
            '12.458036771951139']
    assert [str(r) for r in w] == [
            '0.72552499769865438',
            '1.0634242919791946',
            '0.20669613102835355',
            '0.0043545792937974889']

    x, w = gauss_gen_laguerre(5, 2, 17)
    assert [str(r) for r in x] == [
            '1.0311091440933816',
            '2.8372128239538217',
            '5.6202942725987079',
            '9.6829098376640271',
            '15.828473921690062']
    assert [str(r) for r in w] == [
            '0.52091739683509184',
            '1.0667059331592211',
            '0.38354972366693113',
            '0.028564233532974658',
            '0.00026271280578124935']


def test_gen_laguerre_precise():
    x, w = gauss_gen_laguerre(3, -S.Half, 40)
    assert [str(r) for r in x] == [
            '0.1901635091934881328718554276203028970878',
            '1.784492748543251591186722461957367638500',
            '5.525343742263260275941422110422329464413']
    assert [str(r) for r in w] == [
            '1.449259190448785048183829411195134343108',
            '0.3141346406457132878326231270167565378246',
            '0.009060019811017691281714945129254301865020']

    x, w = gauss_gen_laguerre(3, 2, 40)
    assert [str(r) for r in x] == [
            '1.517387080677412495020323111016672547482',
            '4.311583133719520302881184669723530562299',
            '9.171029785603067202098492219259796890218']
    assert [str(r) for r in w] == [
            '1.037494961490425285817554606541269153041',
            '0.9057500047030653669269785048806009945254',
            '0.05675503380650934725546688857812985243312']


def test_chebyshev_t():
    x, w = gauss_chebyshev_t(1, 17)
    assert [str(r) for r in x] == ['0']
    assert [str(r) for r in w] == ['3.1415926535897932']

    x, w = gauss_chebyshev_t(2, 17)
    assert [str(r) for r in x] == [
            '0.70710678118654752',
            '-0.70710678118654752']
    assert [str(r) for r in w] == [
            '1.5707963267948966',
            '1.5707963267948966']

    x, w = gauss_chebyshev_t(3, 17)
    assert [str(r) for r in x] == [
            '0.86602540378443865',
            '0',
            '-0.86602540378443865']
    assert [str(r) for r in w] == [
            '1.0471975511965977',
            '1.0471975511965977',
            '1.0471975511965977']

    x, w = gauss_chebyshev_t(4, 17)
    assert [str(r) for r in x] == [
            '0.92387953251128676',
            '0.38268343236508977',
            '-0.38268343236508977',
            '-0.92387953251128676']
    assert [str(r) for r in w] == [
            '0.78539816339744831',
            '0.78539816339744831',
            '0.78539816339744831',
            '0.78539816339744831']

    x, w = gauss_chebyshev_t(5, 17)
    assert [str(r) for r in x] == [
            '0.95105651629515357',
            '0.58778525229247313',
            '0',
            '-0.58778525229247313',
            '-0.95105651629515357']
    assert [str(r) for r in w] == [
            '0.62831853071795865',
            '0.62831853071795865',
            '0.62831853071795865',
            '0.62831853071795865',
            '0.62831853071795865']


def test_chebyshev_t_precise():
    x, w = gauss_chebyshev_t(3, 40)
    assert [str(r) for r in x] == [
            '0.8660254037844386467637231707529361834714',
            '0',
            '-0.8660254037844386467637231707529361834714']
    assert [str(r) for r in w] == [
            '1.047197551196597746154214461093167628066',
            '1.047197551196597746154214461093167628066',
            '1.047197551196597746154214461093167628066']


def test_chebyshev_u():
    x, w = gauss_chebyshev_u(1, 17)
    assert [str(r) for r in x] == ['0']
    assert [str(r) for r in w] == ['1.5707963267948966']

    x, w = gauss_chebyshev_u(2, 17)
    assert [str(r) for r in x] == [
            '0.50000000000000000',
            '-0.50000000000000000']
    assert [str(r) for r in w] == [
            '0.78539816339744831',
            '0.78539816339744831']

    x, w = gauss_chebyshev_u(3, 17)
    assert [str(r) for r in x] == [
            '0.70710678118654752',
            '0',
            '-0.70710678118654752']
    assert [str(r) for r in w] == [
            '0.39269908169872415',
            '0.78539816339744831',
            '0.39269908169872415']

    x, w = gauss_chebyshev_u(4, 17)
    assert [str(r) for r in x] == [
            '0.80901699437494742',
            '0.30901699437494742',
            '-0.30901699437494742',
            '-0.80901699437494742']
    assert [str(r) for r in w] == [
            '0.21707871342270599',
            '0.56831944997474231',
            '0.56831944997474231',
            '0.21707871342270599']

    x, w = gauss_chebyshev_u(5, 17)
    assert [str(r) for r in x] == [
            '0.86602540378443865',
            '0.50000000000000000',
            '0',
            '-0.50000000000000000',
            '-0.86602540378443865']
    assert [str(r) for r in w] == [
            '0.13089969389957472',
            '0.39269908169872415',
            '0.52359877559829887',
            '0.39269908169872415',
            '0.13089969389957472']


def test_chebyshev_u_precise():
    x, w = gauss_chebyshev_u(3, 40)
    assert [str(r) for r in x] == [
            '0.7071067811865475244008443621048490392848',
            '0',
            '-0.7071067811865475244008443621048490392848']
    assert [str(r) for r in w] == [
            '0.3926990816987241548078304229099378605246',
            '0.7853981633974483096156608458198757210493',
            '0.3926990816987241548078304229099378605246']


def test_jacobi():
    x, w = gauss_jacobi(1, -S.Half, S.Half, 17)
    assert [str(r) for r in x] == ['0.50000000000000000']
    assert [str(r) for r in w] == ['3.1415926535897932']

    x, w = gauss_jacobi(2, -S.Half, S.Half, 17)
    assert [str(r) for r in x] == [
            '-0.30901699437494742',
            '0.80901699437494742']
    assert [str(r) for r in w] == [
            '0.86831485369082398',
            '2.2732777998989693']

    x, w = gauss_jacobi(3, -S.Half, S.Half, 17)
    assert [str(r) for r in x] == [
            '-0.62348980185873353',
            '0.22252093395631440',
            '0.90096886790241913']
    assert [str(r) for r in w] == [
            '0.33795476356635433',
            '1.0973322242791115',
            '1.7063056657443274']

    x, w = gauss_jacobi(4, -S.Half, S.Half, 17)
    assert [str(r) for r in x] == [
            '-0.76604444311897804',
            '-0.17364817766693035',
            '0.50000000000000000',
            '0.93969262078590838']
    assert [str(r) for r in w] == [
            '0.16333179083642836',
            '0.57690240318269103',
            '1.0471975511965977',
            '1.3541609083740761']

    x, w = gauss_jacobi(5, -S.Half, S.Half, 17)
    assert [str(r) for r in x] == [
            '-0.84125353283118117',
            '-0.41541501300188643',
            '0.14231483827328514',
            '0.65486073394528506',
            '0.95949297361449739']
    assert [str(r) for r in w] == [
            '0.090675770007435371',
            '0.33391416373675607',
            '0.65248870981926643',
            '0.94525424081394926',
            '1.1192597692123861']

    x, w = gauss_jacobi(1, 2, 3, 17)
    assert [str(r) for r in x] == ['0.14285714285714286']
    assert [str(r) for r in w] == ['1.0666666666666667']

    x, w = gauss_jacobi(2, 2, 3, 17)
    assert [str(r) for r in x] == [
            '-0.24025307335204215',
            '0.46247529557426437']
    assert [str(r) for r in w] == [
            '0.48514624517838660',
            '0.58152042148828007']

    x, w = gauss_jacobi(3, 2, 3, 17)
    assert [str(r) for r in x] == [
            '-0.46115870378089762',
            '0.10438533038323902',
            '0.62950064612493132']
    assert [str(r) for r in w] == [
            '0.17937613502213266',
            '0.61595640991147154',
            '0.27133412173306246']

    x, w = gauss_jacobi(4, 2, 3, 17)
    assert [str(r) for r in x] == [
            '-0.59903470850824782',
            '-0.14761105199952565',
            '0.32554377081188859',
            '0.72879429738819258']
    assert [str(r) for r in w] == [
            '0.067809641836772187',
            '0.38956404952032481',
            '0.47995970868024150',
            '0.12933326662932816']

    x, w = gauss_jacobi(5, 2, 3, 17)
    assert [str(r) for r in x] == [
            '-0.69045775012676106',
            '-0.32651993134900065',
            '0.082337849552034905',
            '0.47517887061283164',
            '0.79279429464422850']
    assert [str(r) for r in w] == [
            '0.027410178066337099',
            '0.21291786060364828',
            '0.43908437944395081',
            '0.32220656547221822',
            '0.065047683080512268']


def test_jacobi_precise():
    x, w = gauss_jacobi(3, -S.Half, S.Half, 40)
    assert [str(r) for r in x] == [
            '-0.6234898018587335305250048840042398106323',
            '0.2225209339563144042889025644967947594664',
            '0.9009688679024191262361023195074450511659']
    assert [str(r) for r in w] == [
            '0.3379547635663543330553835737094171534907',
            '1.097332224279111467485302294320899710461',
            '1.706305665744327437921957515249186020246']

    x, w = gauss_jacobi(3, 2, 3, 40)
    assert [str(r) for r in x] == [
            '-0.4611587037808976179121958105554375981274',
            '0.1043853303832390210914918407615869143233',
            '0.6295006461249313240934312425211234110769']
    assert [str(r) for r in w] == [
            '0.1793761350221326596137764371503859752628',
            '0.6159564099114715430909548532229749439714',
            '0.2713341217330624639619353762933057474325']


def test_lobatto():
    x, w = gauss_lobatto(2, 17)
    assert [str(r) for r in x] == [
            '-1',
            '1']
    assert [str(r) for r in w] == [
            '1.0000000000000000',
            '1.0000000000000000']

    x, w = gauss_lobatto(3, 17)
    assert [str(r) for r in x] == [
            '-1',
            '0',
            '1']
    assert [str(r) for r in w] == [
            '0.33333333333333333',
            '1.3333333333333333',
            '0.33333333333333333']

    x, w = gauss_lobatto(4, 17)
    assert [str(r) for r in x] == [
            '-1',
            '-0.44721359549995794',
            '0.44721359549995794',
            '1']
    assert [str(r) for r in w] == [
            '0.16666666666666667',
            '0.83333333333333333',
            '0.83333333333333333',
            '0.16666666666666667']

    x, w = gauss_lobatto(5, 17)
    assert [str(r) for r in x] == [
            '-1',
            '-0.65465367070797714',
            '0',
            '0.65465367070797714',
            '1']
    assert [str(r) for r in w] == [
            '0.10000000000000000',
            '0.54444444444444444',
            '0.71111111111111111',
            '0.54444444444444444',
            '0.10000000000000000']


def test_lobatto_precise():
    x, w = gauss_lobatto(3, 40)
    assert [str(r) for r in x] == [
            '-1',
            '0',
            '1']
    assert [str(r) for r in w] == [
            '0.3333333333333333333333333333333333333333',
            '1.333333333333333333333333333333333333333',
            '0.3333333333333333333333333333333333333333']
