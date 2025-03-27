# Fiches d'exercice Lean pour l'UE Logique et Preuve Assistée

## Démarrage rapide (sur une machine de l'université)

1.  Ouvrez un terminal et tapez les commandes suivantes :

    ```shell
    $ lean
    $ git clone https://github.com/niotie/logique-preuve-assistee.git
    $ export PATH=$PATH:/usr/local/apps/elan/bin
    $ code logique-preuve-assistee
    ```

2.  VSCode vous embête :

    - À la question *Would you like to configure project "logique-preuve-assistee"?*, répondez *"Not now"* ("Pas maintenant").
    - À la question *"CMakeLists.txt was not found in the root of the folder "logique-preuve-assistee". How would you like to proceed?"*, répondez *"Dont'show again"* ("Ne plus montrer cela").
    - À la question *"Configure projects on opening?"* répondez *"Not this workspace"* ("Pas pour ce projet").

3.  Ouvrez le document `EnoncesLPA/TP1LogiqueProp.lean`, VSCode vous embête encore. À la fenêtre surgissante qui s'affiche (*"Lean's version manager Elan is not installed. This means..."*), répondez *"Cancel"* ("Annuler").

4.  Patientez pendant que VSCode démarre l'extension Lean, puis cliquez sur le bouton $\forall$ en haut à droite de la fenêtre, et sélectionnez l'option *"Infoview : Toggle Infoview"*, ou saisissez le raccourci `Ctrl-Shift-Enter`.

Si tout se passe bien, Lean commence à vous donner des indications sur l'état de votre fichier, et vous devriez voir des avertissements (code à compléter, souligné en orange). Baladez votre curseur et regardez ce qui se passe dans la fenêtre "Infoview" à droite...

C'est parti ! Bon courage !

## Utiliser votre ordinateur personnel

Vous pouvez aussi installer Lean sur votre machine personnelle. La procédure est d'installer VSCode (ou VSCodium), puis l'extension Lean 4. Ensuite, clonez le dépôt Git comme indiqué ci-dessus et ouvrez-le dans VSCode, mais cette fois-ci suivez les instructions d'installation plutôt que de les ignorer.

> **Attention :** si vous choisissez de travailler sur votre propre machine, vous ne serez pas prioritaire pour recevoir de l'aide à l'installation ou du service après-vente...

