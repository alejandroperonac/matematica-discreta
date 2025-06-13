import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  static final String[] NOMS = {"ALEJANDRO PERONA CONTI","NOFRE PALMER SEGUI","OSCAR PASCUAL BORDOY"};

  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   */
  static class Tema1 {
    /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
     */
    static final char CONJ = '∧';
    static final char DISJ = '∨';
    static final char IMPL = '→';
    static final char NAND = '.';

    static int exercici1(char[] ops, int[] vars) {
      

    int maxVariable = 0;
    for (int v : vars) {
        if (v + 1 > maxVariable) {
            maxVariable = v + 1;
        }
    }

    boolean allTrue = true;
    boolean allFalse = true;

    int totalStates = 1 << maxVariable;

    for (int state = 0; state < totalStates; state++) {
        boolean[] values = new boolean[maxVariable];
        for (int i = 0; i < maxVariable; i++) {
            values[i] = (state & (1 << i)) != 0;
        }

        boolean result = values[vars[0]];

        for (int i = 0; i < ops.length; i++) {
            boolean nextValue = values[vars[i + 1]];
            char operator = ops[i];

            switch (operator) {
                case '∧': // CONJUNCIÓ
                    result = result && nextValue;
                    break;
                case '∨': // DISJUNCIÓ
                    result = result || nextValue;
                    break;
                case '→': // IMPLICACIÓ
                    result = !result || nextValue;
                    break;
                case '.': // NAND
                    result = !(result && nextValue);
                    break;
                default:
                    throw new IllegalArgumentException("Operador no soportado: " + operator);
            }
        }

        if (result) {
            allFalse = false;
        } else {
            allTrue = false;
        }

        if (!allTrue && !allFalse) {
            break; // No es ni tautología ni contradicción
        }
    }

    if (allTrue) {
        return 1;
    } else if (allFalse) {
        return 0;
    } else {
        return -1;
    }
    }
    
    static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
    // Comprobar si ∀x P(x) es cierto
    boolean allP = true;
    for (int x : universe) {
        if (!p.test(x)) {
            allP = false;
            break;
        }
    }

    // Contar cuántos x cumplen Q(x)
    int countQ = 0;
    for (int x : universe) {
        if (q.test(x)) {
            countQ++;
            if (countQ > 1) break; // no hace falta seguir si ya hay más de uno
        }
    }

    // Comprobar si existe exactamente un x tal que Q(x)
    boolean existsUniqueQ = (countQ == 1);

    // Retornar si (∀x : P(x)) <-> (∃!x : Q(x))
    return allP == existsUniqueQ;
    }

    static void tests() {
      // Exercici 1
      // Taules de veritat

      // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
      test(1, 1, 1, () -> exercici1(new char[] { IMPL, DISJ, DISJ }, new int[] { 0, 2, 1, 0 }) == 1);

      // Contradicció: (p0 . p0) ∧ p0
      test(1, 1, 2, () -> exercici1(new char[] { NAND, CONJ }, new int[] { 0, 0, 0 }) == 0);

      // Exercici 2
      // Equivalència

      test(1, 2, 1, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x == 0, (x) -> x == 0);
      });

      test(1, 2, 2, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x >= 1, (x) -> x % 2 == 0);
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
   */
  static class Tema2 {
    /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
     */
    static int exercici1(int[] a) {
    int n = a.length;

    int[][] stirling = new int[n + 1][n + 1];
    stirling[0][0] = 1;

    for (int i = 1; i <= n; i++) {
      for (int k = 1; k <= i; k++) {
        stirling[i][k] = k * stirling[i - 1][k] + stirling[i - 1][k - 1];
      }
    }

    int bell = 0;
    for (int k = 1; k <= n; k++) {
      bell += stirling[n][k];
    }

    return bell;
    }

 
    

    /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
     */
    static int exercici2(int[] a, int[][] rel) {
    int n = a.length;

    // Creamos matriz booleana para la relación (para hacer clausuras fácilmente)
    boolean[][] R = new boolean[n][n];

    // Mapear valores de a a índices para facilidad
    // Como a está ordenado y es conjunto sin repetidos, podemos buscar índices con binaria o lineal (a[i] == val)
    // Aquí busco índice lineal (podría optimizarse)
    // Función para obtener índice de un valor en a
    java.util.function.IntUnaryOperator idx = (v) -> {
        for (int i = 0; i < n; i++) if (a[i] == v) return i;
        return -1;
    };

    // Inicializar matriz vacía
    for (int i = 0; i < n; i++) 
        for (int j = 0; j < n; j++) 
            R[i][j] = false;

    // Añadir pares de rel (mapeando a índices)
    for (int[] p : rel) {
        int x = idx.applyAsInt(p[0]);
        int y = idx.applyAsInt(p[1]);
        if (x == -1 || y == -1) return -1; // par no en el conjunto
        R[x][y] = true;
    }

    // Clausura reflexiva
    for (int i = 0; i < n; i++) {
        R[i][i] = true;
    }

    // Clausura transitiva (Floyd-Warshall boolean)
    for (int k = 0; k < n; k++) {
        for (int i = 0; i < n; i++) {
            if (R[i][k]) {
                for (int j = 0; j < n; j++) {
                    if (R[k][j]) {
                        R[i][j] = true;
                    }
                }
            }
        }
    }

    // Verificar antisimetría: si (i,j) y (j,i) están en R y i != j, entonces no es orden parcial
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            if (i != j && R[i][j] && R[j][i]) {
                return -1;
            }
        }
    }

    // Contar número de pares en la clausura
    int count = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            if (R[i][j]) count++;
        }
    }

    return count;
}


static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
    int n = a.length;

    // Igual que en ejercicio 2, mapeo valores a índices
    java.util.function.IntUnaryOperator idx = (v) -> {
        for (int i = 0; i < n; i++) if (a[i] == v) return i;
        return -1;
    };

    boolean[][] R = new boolean[n][n];
    for (int i = 0; i < n; i++) 
        for (int j = 0; j < n; j++) 
            R[i][j] = false;

    // Añadir pares de rel (suponemos que es un orden parcial ya)
    for (int[] p : rel) {
        int x1 = idx.applyAsInt(p[0]);
        int y1 = idx.applyAsInt(p[1]);
        if (x1 == -1 || y1 == -1) return null;
        R[x1][y1] = true;
    }

    // Para cada valor de x buscamos índice
    int[] indicesX = new int[x.length];
    for (int i = 0; i < x.length; i++) {
        int ix = idx.applyAsInt(x[i]);
        if (ix == -1) return null;
        indicesX[i] = ix;
    }

    // INFIM (op == false)
    if (!op) {
        // Ínfim: máximo elemento que está debajo de todos los de x
        // Buscamos i en a tal que para todo j en indicesX: R[i][j] == true
        // Y que i sea máximo (no hay k != i con R[i][k] y R[k][j] para todos j)
        // Simplificamos buscando todos los candidatos y elegimos el que no hay otro mayor

        // Paso 1: candidatos i con R[i][j] para todo j
        ArrayList<Integer> candidatos = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            boolean cumple = true;
            for (int j : indicesX) {
                if (!R[i][j]) {
                    cumple = false;
                    break;
                }
            }
            if (cumple) candidatos.add(i);
        }

        // Paso 2: buscar máximo de candidatos: no existe otro candidato mayor que él
        for (int c : candidatos) {
            boolean esMaximo = true;
            for (int c2 : candidatos) {
                if (c != c2 && R[c][c2]) {
                    esMaximo = false;
                    break;
                }
            }
            if (esMaximo) {
                return a[c];
            }
        }

        return null; // no hay ínfim
    } else {
        // SUPREM (op == true)
        // Mínimo elemento que está por encima de todos los de x
        // Buscamos i tal que para todo j: R[j][i] == true
        // Y i mínimo (no hay k != i con R[k][i] y R[j][k] para todos j)

        ArrayList<Integer> candidatos = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            boolean cumple = true;
            for (int j : indicesX) {
                if (!R[j][i]) {
                    cumple = false;
                    break;
                }
            }
            if (cumple) candidatos.add(i);
        }

        // Buscar mínimo candidato: no hay otro candidato menor (candidato k con R[k][i])
        for (int c : candidatos) {
            boolean esMinimo = true;
            for (int c2 : candidatos) {
                if (c != c2 && R[c2][c]) {
                    esMinimo = false;
                    break;
                }
            }
            if (esMinimo) {
                return a[c];
            }
        }

        return null; // no hay suprem
    }
}

    /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
     */
    static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
    int nB = b.length, nA = a.length;

    /* -------- taules auxiliars ---------- */
    // imatges: y = f(x)           (longitud nA)
    int[] img = new int[nA];
    for (int i = 0; i < nA; i++) img[i] = f.apply(a[i]);

    // aparellar y → primer x amb f(x)=y  (per possible inversa dreta)
    int[] primerX = new int[nB];          // −1 si encara no trobat
    for (int i = 0; i < nB; i++) primerX[i] = -1;

    boolean injectiva = true;
    boolean sobrejectiva = true;

    for (int i = 0; i < nA; i++) {
        int y = img[i];

        /* buscar y a b[] */
        int posY = -1;
        for (int j = 0; j < nB; j++)
            if (b[j] == y) { posY = j; break; }

        if (posY == -1) sobrejectiva = false;          // y fora del codomini

        if (posY != -1) {
            if (primerX[posY] == -1) primerX[posY] = a[i];
            else injectiva = false;                    // dos x comparteixen y
        }
    }
    for (int j = 0; j < nB; j++) if (primerX[j] == -1) sobrejectiva = false;

    /* -------- inversa exacta (bijectiva) -------- */
    if (injectiva && sobrejectiva) {
        int[][] inv = new int[nB][2];
        for (int j = 0; j < nB; j++) { inv[j][0] = b[j]; inv[j][1] = primerX[j]; }
        return lexSorted(inv);
    }

    /* -------- inversa per l’esquerra (només injectiva) -------- */
    if (injectiva) {
        int[][] invE = new int[nA][2];                 // un parell per cada x
        for (int i = 0; i < nA; i++) {
            invE[i][0] = img[i];                       // y
            invE[i][1] = a[i];                         // x
        }
        return lexSorted(invE);
    }

    /* -------- inversa per la dreta (només sobrejectiva) -------- */
    if (sobrejectiva) {
        int[][] invD = new int[nB][2];
        for (int j = 0; j < nB; j++) {
            invD[j][0] = b[j];
            invD[j][1] = primerX[j];                   // algun x amb f(x)=y
        }
        return lexSorted(invD);
    }

    return null;                                       // cap inversa vàlida
}

  /*
   * Ordena lexicogràficament un array de 2 dimensions
   */
  static int[][] lexSorted(int[][] arr) {
    if (arr == null) return null;

    int[][] copia = Arrays.copyOf(arr, arr.length);
    Arrays.sort(copia, Arrays::compare);
    return copia;
  }

  /*
   * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfan pred.test(a,b)
   */
  static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
    List<int[]> rel = new ArrayList<>();

    for (int a : as) {
      for (int b : bs) {
        if (pred.test(a, b)) {
          rel.add(new int[] { a, b });
        }
      }
    }

    return rel.toArray(new int[0][0]);
  }

  // Especialització de generateRel per as = bs
  static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
    return generateRel(as, as, pred);
  }

  // Tests simplificats
  public static void main(String[] args) {
    System.out.println("Exercici 1:");
    System.out.println(exercici1(new int[] { 1 }));            // Esperat 1
    System.out.println(exercici1(new int[] { 1, 2, 3 }));      // Esperat 5

    System.out.println("Exercici 2:");
    int[] INT02 = { 0, 1, 2 };
    System.out.println(exercici2(INT02, new int[][] { { 0, 1 }, { 1, 2 } }));                 // Esperat 6
    System.out.println(exercici2(INT02, new int[][] { { 0, 1 }, { 1, 0 }, { 1, 2 } }));       // Esperat -1

    System.out.println("Exercici 3:");
    int[] INT15 = { 1, 2, 3, 4, 5 };
    int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
    System.out.println(exercici3(INT15, DIV15, new int[] { 2, 3 }, false));  // Esperat 1 (ínfim)
    System.out.println(exercici3(INT15, DIV15, new int[] { 2, 3 }, true));   // Esperat null (no suprem)

    System.out.println("Exercici 4:");
    int[] INT05 = { 0, 1, 2, 3, 4, 5 };
    int[] INT02b = { 0, 1, 2 };
    int[][] inv1 = exercici4(INT05, INT02b, x -> x / 2);
    System.out.println(Arrays.deepToString(inv1));

    int[][] inv2 = exercici4(INT02b, INT05, x -> x);
    System.out.println(Arrays.deepToString(inv2));
  }


    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // Nombre de particions

      test(2, 1, 1, () -> exercici1(new int[] { 1 }) == 1);
      test(2, 1, 2, () -> exercici1(new int[] { 1, 2, 3 }) == 5);

      // Exercici 2
      // Clausura d'ordre parcial

      final int[] INT02 = { 0, 1, 2 };

      test(2, 2, 1, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 2} }) == 6);
      test(2, 2, 2, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 0}, {1, 2} }) == -1);

      // Exercici 3
      // Ínfims i suprems

      final int[] INT15 = { 1, 2, 3, 4, 5 };
      final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
      final Integer ONE = 1;

      test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[] { 2, 3 }, false)));
      test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[] { 2, 3 }, true) == null);

      // Exercici 4
      // Inverses

      final int[] INT05 = { 0, 1, 2, 3, 4, 5 };

      test(2, 4, 1, () -> {
        var inv = exercici4(INT05, INT02, (x) -> x/2);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT02.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1]/2 != i)
            return false;
        }

        return true;
      });

      test(2, 4, 2, () -> {
        var inv = exercici4(INT02, INT05, (x) -> x);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT05.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1] != i)
            return false;
        }

        return true;
      });
    }

}

  /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
   */
  static class Tema3 {
   static boolean exercici1(int[][] g) {
    boolean[] visitat = new boolean[g.length];

    for (int v = 0; v < g.length; v++) {
        if (!visitat[v]) {
            if (téCicle(v, -1, visitat, g)) {
                return true;
            }
        }
    }
    return false;
}

static boolean téCicle(int actual, int pare, boolean[] visitat, int[][] g) {
    visitat[actual] = true;

    for (int veí : g[actual]) {
        if (!visitat[veí]) {
            if (téCicle(veí, actual, visitat, g)) {
                return true;
            }
        } else if (veí != pare) {
            return true;
        }
    }

    return false;
}

    /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
     */
    static boolean exercici2(int[][] g1, int[][] g2) {
    int n = g1.length;

    if (g2.length != n)
        return false;

    int[] perm = new int[n];
    for (int i = 0; i < n; i++) perm[i] = i;

    do {
        if (ésIsomorf(g1, g2, perm))
            return true;
    } while (nextPermutation(perm));

    return false;
}

static boolean ésIsomorf(int[][] g1, int[][] g2, int[] perm) {
    int n = g1.length;
    for (int i = 0; i < n; i++) {
        int[] veïns1 = g1[i];
        int[] veïns2 = g2[perm[i]];

        int comptador = 0;
        for (int j = 0; j < n; j++) {
            if (ésVeí(veïns1, j)) {
                if (!ésVeí(veïns2, perm[j]))
                    return false;
                comptador++;
            }
        }

        if (comptador != veïns2.length)
            return false;
    }
    return true;
}

static boolean ésVeí(int[] veïns, int v) {
    for (int i = 0; i < veïns.length; i++) {
        if (veïns[i] == v) return true;
    }
    return false;
}

// Genera la següent permutació lexicogràfica (com la de next_permutation en C++)
static boolean nextPermutation(int[] a) {
    int i = a.length - 2;
    while (i >= 0 && a[i] >= a[i + 1]) i--;

    if (i < 0) return false;

    int j = a.length - 1;
    while (a[j] <= a[i]) j--;

    int temp = a[i]; a[i] = a[j]; a[j] = temp;

    for (int l = i + 1, r = a.length - 1; l < r; l++, r--) {
        temp = a[l]; a[l] = a[r]; a[r] = temp;
    }

    return true;
}

    /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
     */
    static int[] exercici3(int[][] g, int r) {
    int n = g.length;
    boolean[] visitat = new boolean[n];
    List<Integer> postordre = new ArrayList<>();
    boolean[] hiHaCicle = new boolean[1]; // Flag para detectar ciclos

    dfs(r, -1, g, visitat, postordre, hiHaCicle);

    // Si hay ciclo detectado, no es árbol
    if (hiHaCicle[0]) return null;

    // Si algún vértice no fue visitado, no es conexo → no es árbol
    for (int i = 0; i < n; i++) {
        if (!visitat[i]) return null;
    }

    // El número de aristas debe ser n - 1 para ser árbol
    // Contamos las aristas en el grafo
    int edgeCount = 0;
    for (int i = 0; i < n; i++) {
        edgeCount += g[i].length;
    }
    // Como el grafo es no dirigido, cada arista está contada dos veces
    edgeCount /= 2;
    if (edgeCount != n - 1) return null;

    // Convertimos la lista postorden a array (el postorden está en orden correcto)
    int[] resultat = new int[n];
    for (int i = 0; i < n; i++) {
        resultat[i] = postordre.get(i);
    }

    return resultat;
}

static void dfs(int node, int pare, int[][] g, boolean[] visitat, List<Integer> postordre, boolean[] hiHaCicle) {
    visitat[node] = true;
    for (int veí : g[node]) {
        if (!visitat[veí]) {
            dfs(veí, node, g, visitat, postordre, hiHaCicle);
        } else if (veí != pare) {
            // Hay ciclo
            hiHaCicle[0] = true;
        }
    }
    postordre.add(node);
}

    /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
     */
    static int exercici4(char[][] mapa) {
    int files = mapa.length;
    int cols = mapa[0].length;

    int origenX = -1, origenY = -1;
    int destiX = -1, destiY = -1;

    // Cerquem 'O' i 'D'
    for (int i = 0; i < files; i++) {
        for (int j = 0; j < cols; j++) {
            if (mapa[i][j] == 'O') {
                origenX = i;
                origenY = j;
            }
            if (mapa[i][j] == 'D') {
                destiX = i;
                destiY = j;
            }
        }
    }

    if (origenX == -1 || destiX == -1) return -1;

    // BFS
    int[][] dist = new int[files][cols];
    boolean[][] visitat = new boolean[files][cols];
    int[] dx = { -1, 1, 0, 0 }; // amunt, avall, esquerra, dreta
    int[] dy = { 0, 0, -1, 1 };

    int[][] cua = new int[files * cols][2];
    int cap = 0, cuaFi = 0;

    cua[cuaFi][0] = origenX;
    cua[cuaFi][1] = origenY;
    cuaFi++;
    visitat[origenX][origenY] = true;
    dist[origenX][origenY] = 0;

    while (cap < cuaFi) {
        int x = cua[cap][0];
        int y = cua[cap][1];
        cap++;

        if (x == destiX && y == destiY) {
            return dist[x][y];
        }

        for (int d = 0; d < 4; d++) {
            int nx = x + dx[d];
            int ny = y + dy[d];

            if (nx >= 0 && nx < files && ny >= 0 && ny < cols &&
                !visitat[nx][ny] && mapa[nx][ny] != '#') {
                visitat[nx][ny] = true;
                dist[nx][ny] = dist[x][y] + 1;
                cua[cuaFi][0] = nx;
                cua[cuaFi][1] = ny;
                cuaFi++;
            }
        }
    }

    return -1; // si no s'arriba mai a 'D'
}

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {

      final int[][] D2 = { {}, {} };
      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] T1 = { {1, 2}, {0}, {0} };
      final int[][] T2 = { {1}, {0, 2}, {1} };

      // Exercici 1
      // G té cicles?

      test(3, 1, 1, () -> !exercici1(D2));
      test(3, 1, 2, () -> exercici1(C3));

      // Exercici 2
      // Isomorfisme de grafs

      test(3, 2, 1, () -> exercici2(T1, T2));
      test(3, 2, 2, () -> !exercici2(T1, C3));

      // Exercici 3
      // Postordre

      test(3, 3, 1, () -> exercici3(C3, 1) == null);
      test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[] { 1, 2, 0 }));

      // Exercici 4
      // Laberint

      test(3, 4, 1, () -> {
        return -1 == exercici4(new char[][] {
            " #O".toCharArray(),
            "D# ".toCharArray(),
            " # ".toCharArray(),
        });
      });

      test(3, 4, 2, () -> {
        return 8 == exercici4(new char[][] {
            "###D".toCharArray(),
            "O # ".toCharArray(),
            " ## ".toCharArray(),
            "    ".toCharArray(),
        });
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
     */
    static int[] exercici1(String msg, int n, int e) {
      throw new UnsupportedOperationException("pendent");
    }

    /*
     * Primer, desencriptau el missatge utilitzant xifrat RSA amb la clau pública donada. Després
     * descodificau el missatge en blocs de longitud 2 amb codificació ASCII (igual que l'exercici
     * anterior, però al revés).
     *
     * Per construir un String a partir d'un array de bytes podeu fer servir el constructor
     * `new String(byte[])`. Si heu de factoritzar algun nombre, ho podeu fer per força bruta.
     *
     * També podeu suposar que:
     * - La longitud del missatge original és múltiple de 2
     * - El valor de tots els caràcters originals estava entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     */
    static String exercici2(int[] m, int n, int e) {
      throw new UnsupportedOperationException("pendent");
    }

    static void tests() {
      // Exercici 1
      // Codificar i encriptar
      test(4, 1, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = exercici1("Patata", n, e);
        return Arrays.equals(encr, new int[] { 4907, 4785, 4785 });
      });

      // Exercici 2
      // Desencriptar i decodificar
      test(4, 2, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = new int[] { 4907, 4785, 4785 };
        var decr = exercici2(encr, n, e);
        return "Patata".equals(decr);
      });
    }
  }

  /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    System.out.println("---- Tema 1 ----");
    Tema1.tests();
    System.out.println("---- Tema 2 ----");
    Tema2.tests();
    System.out.println("---- Tema 3 ----");
    Tema3.tests();
    System.out.println("---- Tema 4 ----");
    Tema4.tests();
  }

  // Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.
  static void test(int tema, int exercici, int test, BooleanSupplier p) {
    try {
      if (p.getAsBoolean())
        System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
      else
        System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
    } catch (Exception e) {
      if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
        System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
      } else {
        System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
        e.printStackTrace();
      }
    }
  }
}
