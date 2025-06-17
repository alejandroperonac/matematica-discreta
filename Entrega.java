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
      
        // calcular maximo indice de las variables
        int maxVariable = 0;
        for (int v : vars){
            if(v>maxVariable){
            maxVariable = v;
            }
        }
        // el numero de variables sera 1 mas grande que el indice maximo
        int numVariables = maxVariable + 1;
        // el total de combinaciones es igual a: 2^numeroVariables
        int totalCombinaciones = (int) Math.pow((2), numVariables);
        
        boolean[][] combinaciones = generarCombinaciones(numVariables,totalCombinaciones);
        
        boolean resultado;
        boolean tautologia = true;
        boolean contradiccion = true;
        
        for (int i=0;i<totalCombinaciones;i++){
            resultado = combinaciones[i][vars[0]];
            for (int j=0;j<ops.length;j++){
                boolean proximo = combinaciones[i][vars[j+1]];
                resultado = realizarOperacion(resultado,proximo,ops[j]);
            }

            // si es cierto alguna vez significa que no es una contradiccion
            if (resultado) contradiccion=false;
            // si no se cumple alguna vez no es una tautologia
            else tautologia=false;   
        }
        
        if (tautologia) return 1;
        if (contradiccion) return 0;
        return -1;
    }
   
    static boolean[][] generarCombinaciones (int numVariables, int totalCombinaciones) {
        boolean combinaciones[][]= new boolean [totalCombinaciones][numVariables];
           
        for (int i=0; i<totalCombinaciones;i++){
            for (int j=0;j<numVariables;j++){
                // si la variable tiene un 1/0 devolvera true/false
                combinaciones[i][j] = (i / (int) Math.pow(2, j)) % 2 ==1;
            }
        }
        return combinaciones;
    }
    static boolean realizarOperacion(boolean a, boolean b, char operacion){
        
        switch (operacion){
            case CONJ : return a&&b;
            case DISJ : return a || b;
            case IMPL : return !a || b;
            case NAND : return !(a&&b);
            default : return false;
        }
    }

    /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
      
        boolean cumplenP = true;
        // comprobamos para todos los x si se cumple P, si hay alguno que no, devuelve false
        for (int x:universe) {
            if(!p.test(x)) {
                cumplenP=false;
                break;
            }
        }
        
        boolean unicoQ = false;
        int contadorQ = 0;
        // comprobamos la cantidad de x que cumplen Q, devuelve true si hay exactamente 1
        for (int x:universe) {
            if (q.test(x)){
                contadorQ++;
            }
            if (contadorQ>1) {
                break;
            }
        }
        if (contadorQ==1){
            unicoQ=true;
        }
        // si se cumple P y Q o no se cumple ninguno de los dos, devuelve true
        return cumplenP==unicoQ;
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
     
        return numeroBell(a.length);
    }
    static int stirling(int n, int k, int [][]matrizMemoizacion){
        if (k==0 || k>n) return 0;
        if (k==n || k==n) return 1;
        
        if (matrizMemoizacion[n][k] !=-1) return matrizMemoizacion[n][k];
        
        // formula de Stirling
        matrizMemoizacion[n][k]= k* stirling(n-1,k,matrizMemoizacion) + 
        stirling (n-1,k-1,matrizMemoizacion);
        
        return matrizMemoizacion[n][k];    
    }
    static int numeroBell(int n){
        // se crea una tabla para ir guardando los valores de Stirling
        int matrizMemoizacion[][]= new int [n+1][n+1];
        for (int [] fila: matrizMemoizacion) {
            Arrays.fill(fila,-1);
        }
        int total = 0;
        for (int k=1;k<=n;k++) {
            total = total + stirling(n,k,matrizMemoizacion);
        }
        return total;    
    }

    /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
     */
    static int exercici2(int[] a, int[][] rel) {
        int longitud = a.length;

        boolean matrizRelacion[][] = new boolean[longitud][longitud];
        
        for (int pares[]:rel) {
            int i=Arrays.binarySearch(a, pares[0]);
            int j=Arrays.binarySearch(a, pares[1]);
            if (i>=0 && j>=0){
                matrizRelacion[i][j]=true;
            }
        }
        // clausura reflexiva
        for (int i=0;i<longitud;i++) {
            matrizRelacion[i][i] = true;
        }
        // clausura transitiva (algoritmo Warshall)
        for (int i=0;i<longitud;i++){
            for (int j=0;j<longitud;j++){
                for (int k=0;k<longitud;k++) {
                    if (matrizRelacion[j][i] && matrizRelacion[i][k]) {
                        matrizRelacion[j][k] = true;
                    }
                }
            }
        }
        // clausura antisimetrica
        for (int i=0;i<longitud;i++){
            for (int j=0;j<longitud;j++){
                // los elementos no pueden ser simetricos mientras no sean de la forma (a,a)
                if (i!=j && matrizRelacion [i][j] && matrizRelacion [j][i]){
                    return -1;
                }
            }
        }
        int contador = 0;
        for (int i=0;i<longitud;i++){
            for (int j=0;j<longitud;j++){
                if (matrizRelacion[i][j]) contador++;          
            }
        }
        return contador;
    }


    /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
     */
    static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
        
        int longitud=a.length;
        boolean [][] matrizAdyacencia = new boolean [longitud][longitud];
        for (int [] pares:rel){
            int i=-1;
            int j=-1;
            for (int k=0;k<longitud;k++){
                if (a[k]==pares[0]) i = k;
                if (a[k]==pares[1]) j = k;
                
            }
            if (i!=-1 && j!=-1) {
                matrizAdyacencia[i][j]=true;
            }
        }
        // clausura reflexiva
        for (int i=0;i<longitud;i++) {
            matrizAdyacencia[i][i] = true;
        }
        // clausura transitiva (algoritmo Warshall)
        for (int i=0;i<longitud;i++){
            for (int j=0;j<longitud;j++){
                for (int k=0;k<longitud;k++) {
                    if (matrizAdyacencia[j][i] && matrizAdyacencia[i][k]) {
                        matrizAdyacencia[j][k] = true;
                    }
                }
            }
        }
        
        int mejorIndice=-1;
        
        for (int i=0;i<longitud;i++){
            boolean esValido=true;
            
            for (int j=0;j<longitud;j++){
                
                boolean estaEnX=false;
                for (int v:x){
                    if (a[j]==v){
                        estaEnX=true;
                        break;
                    }
                }
                
                if (!estaEnX) continue;
                
                if (op){
                    if (!matrizAdyacencia[j][i]){
                        esValido=false;
                        break;
                    }
                }
                else {
                    if (!matrizAdyacencia[i][j]){
                        esValido=false;
                        break;
                    }
                }
            }
            if (esValido) {
                if (mejorIndice==-1){
                    mejorIndice=i;
                }
                else {
                    if (op){
                        if(matrizAdyacencia[i][mejorIndice]) {
                            mejorIndice=i;
                        }
                    }
                    else {
                        if(matrizAdyacencia[mejorIndice][i]) {
                            mejorIndice=i;
                        }
                    }    
                }
            }     
        }
        
        if (mejorIndice==-1){
            return null;
        }
        else { return a[mejorIndice];
            
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
       
        int longitudA=a.length;
        int longitudB=b.length;
        int []imagen= new int [longitudA];
        
        // guardar imagen en 'a'
        for (int i=0;i<longitudA;i++){
            imagen[i]=f.apply(a[i]);
        }
        // comprobar si es inyectiva
        boolean inyectiva=true;
        for (int i=0;i<longitudA;i++){
            for (int j=i+1;j<longitudA;j++){
                if (imagen[i]==imagen[j]){
                    inyectiva = false;
                    break;
                }
            }
            if (!inyectiva){
                break;
            }    
        }
        
        // si es inyectiva construimos inversa por izquierda extendida
        if (inyectiva) {
            int [][]inversaIzquierda= new int [longitudB][2];
            for (int i=0;i<longitudB;i++){
                int y=b[i];
                int x=a[0];
                
                for (int j=0;j<longitudA;j++){
                    if (imagen[j]==y){
                        x=a[j];
                        break;
                    }
                }
                inversaIzquierda[i][0]=y;
                inversaIzquierda[i][1]=x;
            }
            
            return lexSorted(inversaIzquierda);
        }
        
        // si no es inyectiva construimos la inversa por derecha
        boolean sobreyectiva=true;
        for (int y:b){
            boolean encontrado=false;
            for (int valor:imagen){
                if(valor==y){
                    encontrado=true;
                    break;
                }
            }
            if(!encontrado){
                sobreyectiva=false;
                break;
            }
        }
        
        if (sobreyectiva){
        int [][]inversaDerecha= new int[longitudB][2];
        for (int i=0;i<longitudB;i++){
            int y=b[i];
            int preImagen=-1;
            
            for (int j=0;j<longitudA;j++){
                
                if (imagen[j]==y){
                    preImagen=a[j];
                    break;
                }            
            }
            
            if (preImagen==-1){
                return null;
            }            
            inversaDerecha[i][0]=y;
            inversaDerecha[i][1]=preImagen;
        }
        return lexSorted(inversaDerecha);
    }
        return null;
    }
        
    
    /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null)
        return null;

      var arr2 = Arrays.copyOf(arr, arr.length);
      Arrays.sort(arr2, Arrays::compare);
      return arr2;
    }

    /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
      var rel = new ArrayList<int[]>();

      for (int a : as) {
        for (int b : bs) {
          if (pred.test(a, b)) {
            rel.add(new int[] { a, b });
          }
        }
      }

      return rel.toArray(new int[][] {});
    }

    // Especialització de generateRel per as = bs
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
      return generateRel(as, as, pred);
    }
  
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
    /*
     * Determinau si el graf `g` (no dirigit) té cicles.
     */
    static boolean exercici1(int[][] g) {
        int longitud=g.length;
       
        boolean [] visitado= new boolean [longitud];
        int [] padre = new int [longitud];

        for (int j=0;j<longitud;j++){
            padre[j]=-1;
        } 
        for (int i=0;i<longitud;i++){
            if (!visitado[i]){
                int cima=0;
                int []pila = new int [longitud];
                pila[cima++]=i;
                visitado[i]=true;
                
                while(cima>0){
                    int actual=pila[--cima];
                    for (int vecino:g[actual]){
                        if(!visitado[vecino]){
                            visitado[vecino]=true;
                            pila[cima++]=vecino;
                            padre[vecino]=actual;
                        }
                        else if(padre[actual] != vecino){
                            return true;
                        }
     
                    }        
                }    
            }
        }
        return false;
    }
   

    /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
     */
    static boolean exercici2(int[][] g1, int[][] g2) {
        int longitud=g1.length;
        // si los grafos no tienen el mismo nuemro de vertices no pueden ser isomorfos
        if(longitud!=g2.length){
            return false;
        }
        // convertimos a matrices de adyacencia
        boolean [][] adj1 = new boolean [longitud][longitud];
        boolean [][] adj2 = new boolean [longitud][longitud];
        
        for (int i=0;i<longitud;i++){
            // marcart vecinos en la matriz del grafo 1
            for (int j: g1[i]) {
                adj1[i][j] = true;
            }
            // marcar vecinos en la matriz del grafo 2
            for (int j: g2[i]){
                adj2[i][j] = true;
            }
        }
        int [] perm = new int [longitud];
        boolean [] usado = new boolean [longitud];
        
        return esIsomorfismo(0,longitud,perm,usado,adj1,adj2);
      
    }
    static boolean esIsomorfismo(int pos, int longitud, int [] perm, boolean [] usado, boolean [][]adj1, boolean [][] adj2){
        if (pos==longitud){
            for (int i=0;i<longitud;i++){
                for (int j=0;j<longitud;j++){
                    if (adj1[i][j]!= adj2[perm[i]][perm[j]]){
                        // si alguna arista no se conserva no es isomorfismo
                        return false;
                    }
                
                }
            }
            return true;
        }
        // bucle para probar a asignar cada vertice no usado del grafo 2 a perm[pos]
        for (int v=0;v<longitud;v++){
            if(!usado[v]){
                perm[pos]=v;
                usado[v]=true;
                if (esIsomorfismo(pos+1,longitud,perm,usado,adj1,adj2)){
                    return true;    
                }
                usado[v]=false;
            }
            
        }
        return false;
    }

    /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
     */
    static int[] exercici3(int[][] g, int r) {
        int longitud=g.length;
        boolean [] visitado = new boolean [longitud];
        int [] postorden = new int [longitud];
        int [] contador = {0};
        boolean [] esCiclo = {false};
        
        // realiza recorrido profundo desde el nodo raiz
        recorrerPostorden(g,r,-1,visitado,postorden,contador,esCiclo);
        
        // si ha quedado algun vertice sin visitar no es un arbol
        for (boolean v:visitado){
            if(!v){
                return null;
            }
        }
        // si hay algun ciclo tampoco es un arbol
        if (esCiclo[0]){
            return null;
        }
        return Arrays.copyOf(postorden, contador[0]);

    }
    
    static void recorrerPostorden(int [][]g, int nodo, int padre, boolean [] visitado, 
    int [] postorden, int[] contador, boolean [] esCiclo) {
        
        visitado[nodo]=true;
        // recorremos lista de adyacencia
        for (int vecino: g[nodo]){
            if(!visitado[vecino]){
                recorrerPostorden(g,vecino,nodo,visitado,postorden,contador,esCiclo);
            }    
            else if(vecino!=padre){
                esCiclo[0]=true;
            }    
            
        }
        // añadir en postorden
        postorden[contador[0]++]=nodo;                    
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
        int filas=mapa.length;
        int columnas=mapa[0].length;
        
        int filaInicio=-1;
        int columnaInicio=-1;
        
        // encontrar la posicion del origen
        for (int i=0;i<filas;i++){
            for (int j=0;j<columnas;j++){
                if (mapa[i][j]=='O'){
                    filaInicio=i;
                    columnaInicio=j;
                    break;               
                }
            }
            // si se encuentra el origen salir del bucle
            if (filaInicio!=-1){
                break;
            }
        }
        if (filaInicio==-1){
            return -1;
        }
        
        int tamañoMaximo=filas*columnas;
        // incicializamos arrays que simulan una cola
        int [] filasPendientes = new int [tamañoMaximo];
        int [] columnasPendientes = new int [tamañoMaximo];
        // indice inicio de la cola
        int inicio=0;
        // indice final de la cola
        int fin=0;
        
        // añadimos posicion inicial a la cola
        filasPendientes[fin]=filaInicio;
        columnasPendientes[fin]=columnaInicio;
        fin++;
        
        // inicializamos matriz que guarda la distancia minima desde origen
        // hasta cada celda
        int [][]distancia = new int [filas][columnas];
        for (int i=0;i<filas;i++){
            java.util.Arrays.fill(distancia[i], -1);
        }
        distancia[filaInicio][columnaInicio]=0;
        
        // vectores de desplazamiento a las celdas adyacentes
        int [] filaDesplazar = {-1,1,0,0};
        int [] columnaDesplazar = {0,0,-1,1};
        
        while (inicio<fin){
            int fila = filasPendientes[inicio];
            int columna = columnasPendientes[inicio];
            inicio++;
            
            if (mapa[fila][columna]=='D'){
                return distancia[fila][columna];
            }
            // recorremos las 4 posibles direcciones
            for (int k=0;k<4;k++){
                int nuevaFila=fila + filaDesplazar[k];
                int nuevaColumna=columna+ columnaDesplazar[k];
               
                // comprobamos si la nueva posicion esta dentro del mapa,
                // no la hayamos visitado ya y que no sea una pared               
                if (nuevaFila>=0 && nuevaFila<filas && nuevaColumna >=0 && nuevaColumna <columnas 
                && mapa[nuevaFila][nuevaColumna] != '#' && distancia[nuevaFila][nuevaColumna] ==-1){
                    distancia[nuevaFila][nuevaColumna]= distancia[fila][columna]+1;
                    filasPendientes[fin]= nuevaFila;
                    columnasPendientes[fin]=nuevaColumna;
                    fin++;
                    
                }
            }
        }
        return -1;
             
    }
                
   
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
        int longitud = msg.length();
        int totalBloques = longitud / 2;
        int [] bloquesCifrados = new int [totalBloques];
        for (int bloque=0;bloque<totalBloques;bloque++){
            int posicion= bloque*2;
            
            // leer dos caracteres consecutivos
            int char1=msg.charAt(posicion);
            int char2=msg.charAt(posicion+1);
            // convertir los dos caracteres seguidos a numero
            int numero=char1*128+char2;
            
            // aplicamos la exponenciacion modular
            bloquesCifrados[bloque]= modPow(numero,e,n);
            
        }
        return bloquesCifrados;       
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
        
    // factorizamos n y obtenemos p y q
    int p = 0, q = 0;
    for (int i = 2; i<=Math.sqrt(n); i++) {
        if (n%i == 0){
            p = i;
            q = n / i;
            break;
        }
    }
    // calculamos phi
    int phi = (p - 1) * (q - 1);

    // calculamos el inverso modular de e mod phi
    int d = modInverse(e, phi);
    // cada bloque tiene 2 caracteres
    int longitudMensaje = m.length * 2;
    // inicializamos array de caracteres
    byte[] mensajeCifrado = new byte[longitudMensaje];
    int indice=0;
    for (int bloque:m) {
        
        int descifrado = modPow(bloque, d, n);
        
        // descomposicion con base 128
        int char1 = descifrado / 128;
        int char2 = descifrado % 128;
        // guardar caracteres en el array
        mensajeCifrado[indice++] = (byte) char1;
        mensajeCifrado[indice++] = (byte) char2;  
    }
    // devolvemos el string construido a partir del array de bytes
    return new String(mensajeCifrado);
    }
    
    // metodo de exponenciacion modular eficiente (exponentiation by squaring)
    static int modPow(int base, int exponente, int modulo) {
        
        if (modulo==0){
            return 0;
        }
        // variables long para tener en cuenta decimales a la hora de operar
        long resultado = 1;
        long baseModulo= base%modulo;
        
        // bucle exponenciacion rapida
        while (exponente>0){
            // si el bit menos significativo es 1 es impar
            if (exponente%2 !=0){
                resultado=(resultado*baseModulo) % modulo;
            }
            baseModulo = (baseModulo*baseModulo) % modulo;
            // desplazamos exponente a la derecha
            exponente = exponente / 2;
        }
        return (int) resultado;            
    }
    // metodo con el que calculamos el inverso modular de a modulo m
    static int modInverse(int a, int m) {
       
        int m0=m;
        // coeficientes usados para el encontrar el inverso
        int x0=0;
        int x1=1;
        
        while (a>1){
            int cociente = a / m;
            int temporal = m;
            // actualizamos m con el resto de la division
            m=a%m;
            // guardamos valor temporal
            a= temporal;
            // guardamos valor anterior de x0
            temporal=x0;
            // calculamos nuevo valor a traves de la relacion del algoritmo
            x0= x1 - cociente*x0;
            x1=temporal;
        } 
        // si es negativo lo convertimos a positivo agregandole el modulo inicial
        if (x1<0){
            x1=x1+m0;
        }         
        return x1;  
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
